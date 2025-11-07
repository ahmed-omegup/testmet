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
                if rows.len() > 0 {
                    info!("Received {} replication messages", rows.len());
                }
                for row in rows {
                    if let Ok(data) = row.try_get::<_, Vec<u8>>(2) {
                        info!("Processing message of {} bytes", data.len());
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
            if let Some((id, score)) = parse_insert_message(data) {
                handle_insert(id, score, range_index, storage, registry).await;
            }
        }
        'U' => {
            // Update message
            if let Some((id, score)) = parse_update_message(data) {
                handle_update(id, score, range_index, storage, registry).await;
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

fn parse_insert_message(data: &[u8]) -> Option<(String, i32)> {
    // pgoutput binary format: I\0\0..N\0\u{4}t<len>value1 t<len>value2 t<len>value3 t<len>value4
    // Columns: id (text), name (text), score (int), timestamp (int)
    
    let text = String::from_utf8_lossy(data);
    info!("Parsing INSERT from: {:?}", text);
    
    // Find all text values between 't' markers
    let mut values = Vec::new();
    let mut i = 0;
    while i < data.len() {
        if data[i] == b't' && i + 5 < data.len() {
            // Next 4 bytes are length (big-endian)
            let len = u32::from_be_bytes([data[i+1], data[i+2], data[i+3], data[i+4]]) as usize;
            let start = i + 5;
            if start + len <= data.len() {
                let value = String::from_utf8_lossy(&data[start..start+len]).to_string();
                values.push(value);
                i = start + len;
                continue;
            }
        }
        i += 1;
    }
    
    info!("Parsed values: {:?}", values);
    
    // Extract id (column 0) and score (column 2)
    let id = values.get(0)?.clone();
    let score = values.get(2)?.parse::<i32>().ok()?;
    
    info!("Parsed INSERT: id={}, score={}", id, score);
    Some((id, score))
}

fn parse_update_message(data: &[u8]) -> Option<(String, i32)> {
    // UPDATE format: U\0\0..N or O (new tuple marker)\0\u{4}t<len>value1 t<len>value2 ...
    let text = String::from_utf8_lossy(data);
    
    // Find all text values between 't' markers
    let mut values = Vec::new();
    let mut i = 0;
    while i < data.len() {
        if data[i] == b't' && i + 5 < data.len() {
            let len = u32::from_be_bytes([data[i+1], data[i+2], data[i+3], data[i+4]]) as usize;
            let start = i + 5;
            if start + len <= data.len() {
                let value = String::from_utf8_lossy(&data[start..start+len]).to_string();
                values.push(value);
                i = start + len;
                continue;
            }
        }
        i += 1;
    }
    
    // Extract id (column 0) and score (column 2)
    let id = values.get(0)?.clone();
    let score = values.get(2)?.parse::<i32>().ok()?;
    
    info!("Parsed UPDATE: id={}, score={}", id, score);
    Some((id, score))
}

fn parse_delete_message(data: &[u8]) -> Option<String> {
    // DELETE format: D\0\0..K or O (old tuple marker)\0\u{4}t<len>value
    let text = String::from_utf8_lossy(data);
    
    // Find the first text value
    let mut i = 0;
    while i < data.len() {
        if data[i] == b't' && i + 5 < data.len() {
            let len = u32::from_be_bytes([data[i+1], data[i+2], data[i+3], data[i+4]]) as usize;
            let start = i + 5;
            if start + len <= data.len() {
                let id = String::from_utf8_lossy(&data[start..start+len]).to_string();
                info!("Parsed DELETE: id={}", id);
                return Some(id);
            }
        }
        i += 1;
    }
    
    None
}

async fn handle_insert(
    id: String,
    score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Update storage (we don't need customer_id anymore)
    // Just track the document ID and score
    
    // Find connections interested in this score and notify them
    let connections = {
        let index = range_index.read().await;
        index.find_connections_for_score(score)
    };
    
    for conn_id in connections {
        // Get all queries for this connection and find ones that match the score
        let queries = {
            let index = range_index.read().await;
            index.get_queries_for_connection(&conn_id)
        };
        
        for query in queries {
            if score >= query.min_score && score <= query.max_score {
                info!("Notifying connection {} (query {}) about INSERT: {}", conn_id, query.query_id, id);
                let notification = Notification::Added {
                    query_id: query.query_id,
                    id: id.clone(),
                    score,
                };
                registry.notify(&conn_id, notification).await;
            }
        }
    }
}

async fn handle_update(
    id: String,
    new_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Find connections affected by this update
    let new_connections = {
        let index = range_index.read().await;
        index.find_connections_for_score(new_score)
    };
    
    // Notify connections that have this document in their range
    for conn_id in &new_connections {
        let queries = {
            let index = range_index.read().await;
            index.get_queries_for_connection(conn_id)
        };
        
        for query in queries {
            if new_score >= query.min_score && new_score <= query.max_score {
                info!("Notifying connection {} (query {}) about UPDATE: {}", conn_id, query.query_id, id);
                let notification = Notification::Updated {
                    query_id: query.query_id,
                    id: id.clone(),
                    score: new_score,
                };
                registry.notify(conn_id, notification).await;
            }
        }
    }
}

async fn handle_delete(
    id: String,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // We don't know the score of the deleted document, so we can't find connections easily
    // For now, we'll skip delete notifications
    // In a real implementation, we'd need to track document scores
    info!("DELETE received for {}, but skipping notification (score unknown)", id);
}
