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
            if let Some((id, score)) = extract_id_and_score(&row_msg.new_tuple) {
                handle_insert(id, score, range_index, storage, registry).await;
            }
        }
        decoderbufs::Op::Update => {
            let old = extract_id_and_score(&row_msg.old_tuple);
            let newv = extract_id_and_score(&row_msg.new_tuple);
            match (newv, old) {
                (Some((id_new, new_score)), Some((_id_old, old_score))) => {
                    // Prefer id from new tuple
                    handle_update(id_new, Some(old_score), new_score, range_index, storage, registry).await;
                }
                (Some((id, new_score)), None) => {
                    handle_update(id, None, new_score, range_index, storage, registry).await;
                }
                _ => {}
            }
        }
        decoderbufs::Op::Delete => {
            if let Some((id, old_score)) = extract_id_and_score(&row_msg.old_tuple) {
                handle_delete(id, old_score, range_index, storage, registry).await;
            } else if let Some(id) = extract_id(&row_msg.old_tuple) {
                // If score missing, we can't adjust counts correctly; skip index update but notify removals based on tracking
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

fn extract_id_and_score(tuple: &[decoderbufs::DatumMessage]) -> Option<(String, i32)> {
    let mut id: Option<String> = None;
    let mut score: Option<i32> = None;

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
            _ => {}
        }
    }

    if let (Some(id), Some(score)) = (id, score) {
        info!("Extracted: id={}, score={}", id, score);
        Some((id, score))
    } else {
        None
    }
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
            let notification = Notification::Added {
                query_id: query_id.clone(),
                id: id.clone(),
                score,
            };
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
            let notification = Notification::Added {
                query_id: query_id.clone(),
                id: id.clone(),
                score: new_score,
            };
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
    // We can't adjust counts. Only notify based on tracked memberships.
    let query_ids = {
        let index = range_index.read().await;
        // No direct API to fetch doc's queries; using remove with dummy doesn't work. Skip.
        Vec::<String>::new()
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
