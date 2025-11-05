use tokio_postgres::{Client, NoTls, SimpleQueryMessage};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, error, warn};
use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;

/// Start PostgreSQL logical replication reader
pub async fn start_replication(
    pg_url: String,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
) {
    loop {
        match run_replication(&pg_url, range_index.clone(), storage.clone()).await {
            Ok(_) => {
                info!("Replication ended normally");
                break;
            }
            Err(e) => {
                error!("Replication error: {}, retrying in 5s...", e);
                tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
            }
        }
    }
}

async fn run_replication(
    pg_url: &str,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    // Connect to PostgreSQL
    let (client, connection) = tokio_postgres::connect(pg_url, NoTls).await?;

    // Spawn connection task
    tokio::spawn(async move {
        if let Err(e) = connection.await {
            error!("PostgreSQL connection error: {}", e);
        }
    });

    info!("Connected to PostgreSQL");

    // Create replication slot if not exists
    setup_replication_slot(&client).await?;

    // Start consuming changes
    consume_changes(client, range_index, storage).await?;

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
            .simple_query("SELECT pg_create_logical_replication_slot('btree_pubsub_slot', 'test_decoding')")
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
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    info!("Starting to consume logical replication stream...");

    // Subscribe to changes from the 'docs' table using test_decoding
    let query = "SELECT * FROM pg_logical_slot_get_changes('btree_pubsub_slot', NULL, NULL)";

    loop {
        match client.simple_query(query).await {
            Ok(messages) => {
                for message in messages {
                    if let SimpleQueryMessage::Row(row) = message {
                        // Parse WAL data
                        // Format: lsn | xid | data
                        if let Some(data) = row.get(2) {
                            process_wal_event(data, &range_index, &storage).await;
                        }
                    }
                }
            }
            Err(e) => {
                warn!("Error reading changes: {}", e);
            }
        }

        // Small delay to avoid spinning
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
}

async fn process_wal_event(
    data: &str,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
) {
    // Parse test_decoding output format
    // Example: "table public.docs: INSERT: id[text]:'doc_1' score[integer]:500 name[text]:'doc_1' timestamp[bigint]:0"
    
    if !data.contains("table public.docs") {
        return;
    }

    let operation = if data.contains("INSERT:") {
        "insert"
    } else if data.contains("UPDATE:") {
        "update"
    } else if data.contains("DELETE:") {
        "delete"
    } else {
        return;
    };

    // Extract fields
    let score = extract_field(data, "score");
    let id = extract_string_field(data, "id");
    let timestamp = extract_field(data, "timestamp");

    if let (Some(score), Some(id)) = (score, id) {
        // Find all connections interested in this score
        let connections = {
            let index = range_index.read().await;
            index.find_connections_for_score(score)
        };

        info!(
            "Event: {} doc={} score={} timestamp={:?} -> {} connections",
            operation,
            id,
            score,
            timestamp,
            connections.len()
        );

        // Update storage and send to connections
        for conn_id in connections {
            let queries = {
                let index = range_index.read().await;
                index.get_queries_for_connection(&conn_id)
            };

            for query in queries {
                if score >= query.min_score && score <= query.max_score {
                    match operation {
                        "insert" | "update" => {
                            if let Err(e) = storage.add_document_to_connection(&conn_id, &query.query_id, &id) {
                                error!("Failed to add document to connection: {}", e);
                            }
                        }
                        "delete" => {
                            if let Err(e) = storage.remove_document_from_connection(&conn_id, &query.query_id, &id) {
                                error!("Failed to remove document from connection: {}", e);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
}

fn extract_field(data: &str, field: &str) -> Option<i32> {
    // Simple extraction: "score[integer]:500"
    if let Some(start) = data.find(&format!("{}[", field)) {
        if let Some(colon) = data[start..].find(':') {
            let value_start = start + colon + 1;
            if let Some(end) = data[value_start..].find(|c: char| !c.is_numeric() && c != '-') {
                return data[value_start..value_start + end].parse().ok();
            } else {
                return data[value_start..].trim().parse().ok();
            }
        }
    }
    None
}

fn extract_string_field(data: &str, field: &str) -> Option<String> {
    // Extract string field: "id[text]:'doc_123'"
    if let Some(start) = data.find(&format!("{}[", field)) {
        if let Some(colon) = data[start..].find(':') {
            let value_start = start + colon + 1;
            let rest = &data[value_start..];
            // Skip leading quote
            if rest.starts_with('\'') {
                if let Some(end) = rest[1..].find('\'') {
                    return Some(rest[1..1 + end].to_string());
                }
            }
        }
    }
    None
}
