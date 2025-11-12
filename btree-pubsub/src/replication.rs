use tokio_postgres::{Client, NoTls};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, error, warn};
use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;
use crate::connection_registry::{ConnectionRegistry, Notification};
use prost::Message;

// Include the generated protobuf code
mod decoderbufs {
    include!(concat!(env!("OUT_DIR"), "/decoderbufs.rs"));
}

/// Start PostgreSQL logical replication reader
pub async fn start_replication(
    pg_url: String,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    registry: Arc<ConnectionRegistry>,
) {
    // Run replication - any error is fatal
    if let Err(e) = run_replication(&pg_url, range_index, storage, registry).await {
        error!("Fatal replication error: {}", e);
        std::process::exit(1);
    }
}

async fn run_replication(
    pg_url: &str,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    registry: Arc<ConnectionRegistry>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    // Connect to PostgreSQL
    let (client, connection) = tokio_postgres::connect(pg_url, NoTls).await?;

    // Spawn connection task
    tokio::spawn(async move {
        if let Err(e) = connection.await {
            error!("PostgreSQL connection error: {}", e);
        }
    });

    info!("Connected to PostgreSQL for replication");

    // Create replication slot if not exists
    setup_replication_slot(&client).await?;

    // Start consuming changes
    consume_changes(client, range_index, storage, registry).await?;

    Ok(())
}

async fn setup_replication_slot(client: &Client) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    // Check if slot exists
    let rows = client
        .query(
            "SELECT * FROM pg_replication_slots WHERE slot_name = 'btree_pubsub_slot'",
            &[],
        )
        .await?;

    if rows.is_empty() {
        info!("Creating replication slot...");
        client
            .simple_query("SELECT pg_create_logical_replication_slot('btree_pubsub_slot', 'decoderbufs')")
            .await?;
        info!("Replication slot created");
    } else {
        info!("Replication slot already exists");
    }

    Ok(())
}

async fn consume_changes(
    client: Client,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    registry: Arc<ConnectionRegistry>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    info!("Starting to consume logical replication stream...");

    let query = "SELECT lsn, xid, data FROM pg_logical_slot_get_binary_changes('btree_pubsub_slot', NULL, NULL)";

    loop {
        match client.query(query, &[]).await {
            Ok(rows) => {
                if rows.len() > 0 {
                    info!("Received {} replication messages", rows.len());
                }
                for row in rows {
                    if let Ok(data) = row.try_get::<_, Vec<u8>>(2) {
                        info!("Processing message of {} bytes", data.len());
                        process_decoderbufs_message(&data, &range_index, &storage, &registry).await;
                    }
                }
            }
            Err(e) => {
                error!("Fatal error reading changes: {:?}", e);
                return Err(e.into());
            }
        }

        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
}

// Process decoderbufs protobuf message
async fn process_decoderbufs_message(
    data: &[u8],
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    if data.is_empty() {
        return;
    }

    // Decode protobuf message
    let row_msg = match decoderbufs::RowMessage::decode(data) {
        Ok(msg) => msg,
        Err(e) => {
            error!("Failed to decode protobuf message: {}", e);
            return;
        }
    };

    // Check operation type
    let op = row_msg.op();
    
    match op {
        decoderbufs::Op::Insert => {
            if let Some((id, score_opt, ts_opt)) = extract_id_score_ts(&row_msg.new_tuple) {
                if let Some(score) = score_opt {
                    handle_insert(id, score, ts_opt.unwrap_or(0), range_index, storage, registry).await;
                }
            }
        }
        decoderbufs::Op::Update => {
            let old = extract_id_score_ts(&row_msg.old_tuple);
            let newv = extract_id_score_ts(&row_msg.new_tuple);
            match (newv, old) {
                (Some((id_new, new_score_opt, new_ts_opt)), Some((_id_old, old_score_opt, _))) => {
                    if let Some(new_score) = new_score_opt {
                        handle_update(id_new.clone(), old_score_opt, new_score, range_index, storage, registry).await;
                    }
                    if let Some(ts) = new_ts_opt { 
                        if ts == -1 { 
                            info!("Broadcasting timestamp update for doc: {}, ts={}", id_new, ts);
                            broadcast_timestamp_update(&id_new, ts, range_index, registry).await; 
                        } 
                    }
                }
                (Some((id, new_score_opt, new_ts_opt)), None) => {
                    if let Some(new_score) = new_score_opt {
                        handle_update(id.clone(), None, new_score, range_index, storage, registry).await;
                    }
                    if let Some(ts) = new_ts_opt { if ts == -1 { broadcast_timestamp_update(&id, ts, range_index, registry).await; } }
                }
                _ => {}
            }
        }
        decoderbufs::Op::Delete => {
            if let Some((id, old_score_opt, _)) = extract_id_score_ts(&row_msg.old_tuple) {
                if let Some(old_score) = old_score_opt {
                    handle_delete(id, old_score, range_index, storage, registry).await;
                } else if let Some(id2) = extract_id(&row_msg.old_tuple) {
                    handle_delete_no_value(id2, range_index, storage, registry).await;
                }
            } else if let Some(id) = extract_id(&row_msg.old_tuple) {
                handle_delete_no_value(id, range_index, storage, registry).await;
            }
        }
        decoderbufs::Op::Begin | decoderbufs::Op::Commit => {
            // Transaction markers - ignore
        }
        _ => {
            warn!("Unknown operation type: {:?}", op);
        }
    }
}

fn extract_id_score_ts(tuple: &[decoderbufs::DatumMessage]) -> Option<(String, Option<i32>, Option<i32>)> {
    let mut id: Option<String> = None;
    let mut score: Option<i32> = None;
    let mut timestamp: Option<i32> = None;

    for datum in tuple {
        let col_name = datum.column_name.as_ref()?;
        
        match col_name.as_str() {
            "id" => {
                if let Some(decoderbufs::datum_message::Datum::DatumString(ref s)) = datum.datum {
                    id = Some(s.clone());
                }
            }
            "score" => {
                if let Some(decoderbufs::datum_message::Datum::DatumInt32(s)) = datum.datum {
                    score = Some(s);
                } else if let Some(decoderbufs::datum_message::Datum::DatumInt64(s)) = datum.datum {
                    score = Some(s as i32);
                }
            }
            "timestamp" => {
                if let Some(decoderbufs::datum_message::Datum::DatumInt32(t)) = datum.datum {
                    timestamp = Some(t);
                } else if let Some(decoderbufs::datum_message::Datum::DatumInt64(t)) = datum.datum {
                    timestamp = Some(t as i32);
                }
            }
            _ => {}
        }
    }
    let result = id.map(|idv| (idv, score, timestamp));
    if let Some((ref id_val, ref score_val, ref ts_val)) = result {
        info!("Extracted: id={}, score={:?}, timestamp={:?}", id_val, score_val, ts_val);
    }
    result
}

fn extract_id(tuple: &[decoderbufs::DatumMessage]) -> Option<String> {
    for datum in tuple {
        if let Some(ref col_name) = datum.column_name {
            if col_name == "id" {
                if let Some(decoderbufs::datum_message::Datum::DatumString(ref s)) = datum.datum {
                    info!("Extracted DELETE id={}", s);
                    return Some(s.clone());
                }
            }
        }
    }
    None
}

async fn handle_insert(
    id: String,
    score: i32,
    timestamp: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Get queries this document matches
    let matches = {
        let mut index = range_index.write().await;
        index.get_queries_for_change(&id, None, score as f64, 1)
    };

    // Notify all subscribed connections for each query
    for query_id in matches.added_to {
        let conns = {
            let index = range_index.read().await;
            index.get_connections_for_query(&query_id)
        };
        for conn_id in conns {
            info!("Notifying connection {} (query {}) about INSERT: {}", conn_id, query_id, id);
            let notification = Notification::Added { query_id: query_id.clone(), id: id.clone(), score, timestamp };
            registry.notify(&conn_id, notification).await;
        }
    }
}

async fn handle_update(
    id: String,
    old_score: Option<i32>,
    new_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Get queries this document was added to or removed from
    let matches = {
        let mut index = range_index.write().await;
        index.get_queries_for_change(&id, old_score.map(|s| s as f64), new_score as f64, 1)
    };

    // Notify about additions
    for query_id in matches.added_to {
        let conns = {
            let index = range_index.read().await;
            index.get_connections_for_query(&query_id)
        };
        for conn_id in conns {
            info!("Notifying connection {} (query {}) about ADD (update): {}", conn_id, query_id, id);
            let notification = Notification::Added { query_id: query_id.clone(), id: id.clone(), score: new_score, timestamp: 0 };
            registry.notify(&conn_id, notification).await;
        }
    }

    // Notify about removals
    for query_id in matches.removed_from {
        let conns = {
            let index = range_index.read().await;
            index.get_connections_for_query(&query_id)
        };
        for conn_id in conns {
            info!("Notifying connection {} (query {}) about REMOVE (update): {}", conn_id, query_id, id);
            let notification = Notification::Removed {
                query_id: query_id.clone(),
                id: id.clone(),
            };
            registry.notify(&conn_id, notification).await;
        }
    }
}

async fn handle_delete(
    id: String,
    old_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Remove from index and get queries it was part of
    let query_ids = {
        let mut index = range_index.write().await;
        index.remove_document(&id, old_score as f64, 1)
    };

    for query_id in query_ids {
        let conns = {
            let index = range_index.read().await;
            index.get_connections_for_query(&query_id)
        };
        for conn_id in conns {
            info!("Notifying connection {} (query {}) about DELETE: {}", conn_id, query_id, id);
            let notification = Notification::Removed {
                query_id: query_id.clone(),
                id: id.clone(),
            };
            registry.notify(&conn_id, notification).await;
        }
    }
}

async fn handle_delete_no_value(
    id: String,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    let query_ids = {
        let index = range_index.read().await;
        index.get_tracked_queries_for_document(&id)
    };
    for query_id in query_ids {
        let conns = {
            let index = range_index.read().await;
            index.get_connections_for_query(&query_id)
        };
        for conn_id in conns {
            let notification = Notification::Removed { query_id: query_id.clone(), id: id.clone() };
            registry.notify(&conn_id, notification).await;
        }
    }
}

async fn broadcast_timestamp_update(
    id: &str,
    timestamp: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    registry: &Arc<ConnectionRegistry>,
) {
    let query_ids = {
        let index = range_index.read().await;
        index.get_tracked_queries_for_document(id)
    };
    for query_id in query_ids {
        let conns = {
            let index = range_index.read().await;
            index.get_connections_for_query(&query_id)
        };
        for conn_id in conns {
            let notification = Notification::Updated { query_id: query_id.clone(), id: id.to_string(), score: 0, timestamp };
            registry.notify(&conn_id, notification).await;
        }
    }
}
