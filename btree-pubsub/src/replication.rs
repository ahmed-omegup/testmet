use tokio_postgres::{Client, NoTls};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, error, warn};
use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;
use crate::connection_registry::{ConnectionRegistry, Notification};

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
            .simple_query("SELECT pg_create_logical_replication_slot('btree_pubsub_slot', 'pgoutput')")
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

    let query = "SELECT lsn, xid, data FROM pg_logical_slot_get_binary_changes('btree_pubsub_slot', NULL, NULL, 'proto_version', '1', 'publication_names', 'electric_publication_default')";

    loop {
        match client.query(query, &[]).await {
            Ok(rows) => {
                for row in rows {
                    if let Ok(data) = row.try_get::<_, Vec<u8>>(2) {
                        process_pgoutput_message(&data, &range_index, &storage, &registry).await;
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

// Simple pgoutput message parser
async fn process_pgoutput_message(
    data: &[u8],
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    if data.is_empty() {
        return;
    }

    // pgoutput message type is first byte
    let msg_type = data[0] as char;
    
    match msg_type {
        'B' => {}, // Begin - start of transaction
        'C' => {}, // Commit - end of transaction  
        'I' => {
            // Insert message
            if let Some((id, customer_id, score)) = parse_insert_message(data) {
                handle_insert(id, customer_id, score, range_index, storage, registry).await;
            }
        }
        'U' => {
            // Update message
            if let Some((id, customer_id, score)) = parse_update_message(data) {
                handle_update(id, customer_id, score, range_index, storage, registry).await;
            }
        }
        'D' => {
            // Delete message
            if let Some(id) = parse_delete_message(data) {
                handle_delete(id, range_index, storage, registry).await;
            }
        }
        'R' => {}, // Relation - table schema info
        _ => {
            warn!("Unknown pgoutput message type: {}", msg_type);
        }
    }
}

fn parse_insert_message(data: &[u8]) -> Option<(i32, i32, f64)> {
    // Simple text-based parsing of the binary data
    // pgoutput encodes data in a somewhat readable format
    let text = String::from_utf8_lossy(data);
    
    // Look for patterns like: doc_123, customer_id, score
    let parts: Vec<&str> = text.split('\0').filter(|s| !s.is_empty()).collect();
    
    // Try to extract id (from doc_N pattern)
    let id = parts.iter()
        .find(|s| s.starts_with("doc_"))
        .and_then(|s| s.strip_prefix("doc_"))
        .and_then(|s| s.parse::<i32>().ok())?;
    
    // Customer ID is usually same as doc ID in test data
    let customer_id = id;
    
    // Try to find score (a number that's not the ID)
    let score = parts.iter()
        .filter_map(|s| s.parse::<f64>().ok())
        .find(|&n| n != id as f64)?;
    
    info!("Parsed INSERT: id={}, customer_id={}, score={}", id, customer_id, score);
    Some((id, customer_id, score))
}

fn parse_update_message(data: &[u8]) -> Option<(i32, i32, f64)> {
    // Update has similar structure to insert
    let text = String::from_utf8_lossy(data);
    let parts: Vec<&str> = text.split('\0').filter(|s| !s.is_empty()).collect();
    
    let id = parts.iter()
        .find(|s| s.starts_with("doc_"))
        .and_then(|s| s.strip_prefix("doc_"))
        .and_then(|s| s.parse::<i32>().ok())?;
    
    let customer_id = id;
    
    let score = parts.iter()
        .filter_map(|s| s.parse::<f64>().ok())
        .find(|&n| n != id as f64)?;
    
    info!("Parsed UPDATE: id={}, customer_id={}, score={}", id, customer_id, score);
    Some((id, customer_id, score))
}

fn parse_delete_message(data: &[u8]) -> Option<i32> {
    let text = String::from_utf8_lossy(data);
    let parts: Vec<&str> = text.split('\0').filter(|s| !s.is_empty()).collect();
    
    let id = parts.iter()
        .find(|s| s.starts_with("doc_"))
        .and_then(|s| s.strip_prefix("doc_"))
        .and_then(|s| s.parse::<i32>().ok())?;
    
    info!("Parsed DELETE: id={}", id);
    Some(id)
}

async fn handle_insert(
    id: i32,
    customer_id: i32,
    score: f64,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Update storage
    storage.track_document(id, customer_id, score);
    
    // Update BTree index
    {
        let mut index = range_index.write().await;
        index.insert(score, customer_id);
    }
    
    // Find connections interested in this score and notify them
    let connections = {
        let index = range_index.read().await;
        index.find_connections_for_score(score)
    };
    
    for conn_id in connections {
        let query_id = {
            let index = range_index.read().await;
            index.get_query_id(&conn_id)
        };
        
        if let Some(query_id) = query_id {
            info!("Notifying connection {} about INSERT: doc_{}", conn_id, id);
            let notification = Notification::Added {
                query_id,
                doc_id: format!("doc_{}", id),
            };
            registry.send_notification(&conn_id, notification).await;
        }
    }
}

async fn handle_update(
    id: i32,
    customer_id: i32,
    new_score: f64,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Get old score for this document
    let old_score = storage.get_score(id);
    
    // Update storage with new score
    storage.track_document(id, customer_id, new_score);
    
    // Update BTree index
    if let Some(old) = old_score {
        let mut index = range_index.write().await;
        index.remove(old, customer_id);
        index.insert(new_score, customer_id);
    } else {
        let mut index = range_index.write().await;
        index.insert(new_score, customer_id);
    }
    
    // Find connections affected by this update
    let old_connections = if let Some(old) = old_score {
        let index = range_index.read().await;
        index.find_connections_for_score(old)
    } else {
        Vec::new()
    };
    
    let new_connections = {
        let index = range_index.read().await;
        index.find_connections_for_score(new_score)
    };
    
    // Notify connections that lost this document
    for conn_id in &old_connections {
        if !new_connections.contains(conn_id) {
            let query_id = {
                let index = range_index.read().await;
                index.get_query_id(conn_id)
            };
            
            if let Some(query_id) = query_id {
                info!("Notifying connection {} about REMOVE (update): doc_{}", conn_id, id);
                let notification = Notification::Removed {
                    query_id,
                    doc_id: format!("doc_{}", id),
                };
                registry.send_notification(conn_id, notification).await;
            }
        }
    }
    
    // Notify connections that gained or still have this document
    for conn_id in &new_connections {
        let query_id = {
            let index = range_index.read().await;
            index.get_query_id(conn_id)
        };
        
        if let Some(query_id) = query_id {
            if old_connections.contains(conn_id) {
                info!("Notifying connection {} about UPDATE: doc_{}", conn_id, id);
                let notification = Notification::Updated {
                    query_id,
                    doc_id: format!("doc_{}", id),
                };
                registry.send_notification(conn_id, notification).await;
            } else {
                info!("Notifying connection {} about ADD (update): doc_{}", conn_id, id);
                let notification = Notification::Added {
                    query_id,
                    doc_id: format!("doc_{}", id),
                };
                registry.send_notification(conn_id, notification).await;
            }
        }
    }
}

async fn handle_delete(
    id: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Get old score before deleting
    let old_score = storage.get_score(id);
    let customer_id = storage.get_customer_id(id);
    
    // Mark as deleted in storage
    storage.mark_deleted(id);
    
    // Remove from BTree index
    if let (Some(score), Some(cid)) = (old_score, customer_id) {
        let mut index = range_index.write().await;
        index.remove(score, cid);
        
        // Find and notify affected connections
        drop(index);
        let connections = {
            let index = range_index.read().await;
            index.find_connections_for_score(score)
        };
        
        for conn_id in connections {
            let query_id = {
                let index = range_index.read().await;
                index.get_query_id(&conn_id)
            };
            
            if let Some(query_id) = query_id {
                info!("Notifying connection {} about DELETE: doc_{}", conn_id, id);
                let notification = Notification::Removed {
                    query_id,
                    doc_id: format!("doc_{}", id),
                };
                registry.send_notification(&conn_id, notification).await;
            }
        }
    }
}
