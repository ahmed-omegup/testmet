use tokio_postgres::{Client, NoTls, SimpleQueryMessage};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, error, warn};
use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;
use crate::connection_registry::{ConnectionRegistry, Notification};
use bytes::{Buf, Bytes};

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
    // Connect to PostgreSQL with notice filter
    let (client, connection) = tokio_postgres::connect(pg_url, NoTls).await?;

    // Spawn connection task and suppress notices
    tokio::spawn(async move {
        if let Err(e) = connection.await {
            error!("PostgreSQL connection error: {}", e);
        }
    });

    info!("Connected to PostgreSQL");

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

    // Subscribe to changes using decoderbufs (outputs protobuf)
    let query = "SELECT data FROM pg_logical_slot_get_binary_changes('btree_pubsub_slot', NULL, NULL)";

    loop {
        match client.query(query, &[]).await {
            Ok(rows) => {
                for row in rows {
                    if let Ok(data) = row.try_get::<_, Vec<u8>>(0) {
                        process_protobuf_event(&data, &range_index, &storage, &registry).await;
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

async fn process_protobuf_event(
    data: &[u8],
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
) {
    // Decode decoderbufs protobuf format
    // Simplified decoding - decoderbufs uses a nested structure
    
    let mut buf = Bytes::copy_from_slice(data);
    
    // Try to parse the message
    if let Some((table_name, op, id, score)) = parse_decoderbufs_message(&mut buf) {
        if table_name != "docs" {
            return;
        }

        let operation = match op {
            1 => "insert",
            2 => "update",
            3 => "delete",
            _ => return,
        };

        // Find all connections interested in this score
        let connections = {
            let index = range_index.read().await;
            index.find_connections_for_score(score)
        };

        info!(
            "Event: {} doc={} score={} -> {} connections",
            operation, id, score, connections.len()
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
                        "insert" => {
                            if let Err(e) = storage.add_document_to_connection(&conn_id, &query.query_id, &id) {
                                error!("Failed to add document to connection: {}", e);
                            } else {
                                // Send Added notification
                                registry.notify(
                                    &conn_id,
                                    Notification::Added {
                                        query_id: query.query_id.clone(),
                                        id: id.clone(),
                                        score,
                                    },
                                ).await;
                            }
                        }
                        "update" => {
                            if let Err(e) = storage.add_document_to_connection(&conn_id, &query.query_id, &id) {
                                error!("Failed to update document in connection: {}", e);
                            } else {
                                // Send Updated notification
                                registry.notify(
                                    &conn_id,
                                    Notification::Updated {
                                        query_id: query.query_id.clone(),
                                        id: id.clone(),
                                        score,
                                    },
                                ).await;
                            }
                        }
                        "delete" => {
                            if let Err(e) = storage.remove_document_from_connection(&conn_id, &query.query_id, &id) {
                                error!("Failed to remove document from connection: {}", e);
                            } else {
                                // Send Removed notification
                                registry.notify(
                                    &conn_id,
                                    Notification::Removed {
                                        query_id: query.query_id.clone(),
                                        id: id.clone(),
                                    },
                                ).await;
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
}

// Simple protobuf parser for decoderbufs format
fn parse_decoderbufs_message(buf: &mut Bytes) -> Option<(String, u32, String, i32)> {
    // Decoderbufs message structure (simplified):
    // Field 1: operation (INSERT=1, UPDATE=2, DELETE=3)
    // Field 2: schema
    // Field 3: table
    // Field 4: columns (repeated)
    
    let mut operation = 0u32;
    let mut table_name = String::new();
    let mut id_value = String::new();
    let mut score_value = 0i32;
    
    while buf.remaining() > 0 {
        // Read field tag
        let tag = match prost::encoding::decode_varint(buf) {
            Ok(v) => v,
            Err(_) => break,
        };
        
        let field_num = (tag >> 3) as u32;
        let wire_type = (tag & 0x7) as u32;
        
        match field_num {
            1 => {
                // operation
                if wire_type == 0 {
                    operation = prost::encoding::decode_varint(buf).ok()? as u32;
                }
            }
            3 => {
                // table name
                if wire_type == 2 {
                    let len = prost::encoding::decode_varint(buf).ok()? as usize;
                    if buf.remaining() >= len {
                        table_name = String::from_utf8_lossy(&buf.copy_to_bytes(len)).to_string();
                    }
                }
            }
            4 => {
                // columns (repeated)
                if wire_type == 2 {
                    let len = prost::encoding::decode_varint(buf).ok()? as usize;
                    if buf.remaining() >= len {
                        let mut col_buf = buf.copy_to_bytes(len);
                        if let Some((name, value)) = parse_column(&mut col_buf) {
                            if name == "id" {
                                id_value = value.clone();
                            } else if name == "score" {
                                score_value = value.parse().unwrap_or(0);
                            }
                        }
                    }
                }
            }
            _ => {
                // Skip unknown fields
                skip_field(buf, wire_type)?;
            }
        }
    }
    
    if !table_name.is_empty() && !id_value.is_empty() {
        Some((table_name, operation, id_value, score_value))
    } else {
        None
    }
}

fn parse_column(buf: &mut Bytes) -> Option<(String, String)> {
    let mut col_name = String::new();
    let mut col_value = String::new();
    
    while buf.remaining() > 0 {
        let tag = prost::encoding::decode_varint(buf).ok()?;
        let field_num = (tag >> 3) as u32;
        let wire_type = (tag & 0x7) as u32;
        
        match field_num {
            1 => {
                // column name
                if wire_type == 2 {
                    let len = prost::encoding::decode_varint(buf).ok()? as usize;
                    if buf.remaining() >= len {
                        col_name = String::from_utf8_lossy(&buf.copy_to_bytes(len)).to_string();
                    }
                }
            }
            5 => {
                // column value (string)
                if wire_type == 2 {
                    let len = prost::encoding::decode_varint(buf).ok()? as usize;
                    if buf.remaining() >= len {
                        col_value = String::from_utf8_lossy(&buf.copy_to_bytes(len)).to_string();
                    }
                }
            }
            _ => {
                skip_field(buf, wire_type)?;
            }
        }
    }
    
    if !col_name.is_empty() {
        Some((col_name, col_value))
    } else {
        None
    }
}

fn skip_field(buf: &mut Bytes, wire_type: u32) -> Option<()> {
    match wire_type {
        0 => {
            // Varint
            prost::encoding::decode_varint(buf).ok()?;
        }
        1 => {
            // 64-bit
            if buf.remaining() >= 8 {
                buf.advance(8);
            } else {
                return None;
            }
        }
        2 => {
            // Length-delimited
            let len = prost::encoding::decode_varint(buf).ok()? as usize;
            if buf.remaining() >= len {
                buf.advance(len);
            } else {
                return None;
            }
        }
        5 => {
            // 32-bit
            if buf.remaining() >= 4 {
                buf.advance(4);
            } else {
                return None;
            }
        }
        _ => return None,
    }
    Some(())
}
