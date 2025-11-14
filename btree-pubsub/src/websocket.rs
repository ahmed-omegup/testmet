use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{accept_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use serde::{Deserialize, Serialize};
use tracing::{info, error, warn};
use uuid::Uuid;

use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;
use crate::connection_registry::{ConnectionRegistry, Notification};
use crate::retrieval_job::RetrievalJobIndex;
use crate::doc_index::DocIndex;

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum ClientMessage {
    #[serde(rename = "subscribe")]
    Subscribe {
        min_score: i32,
        max_score: i32,
    },
    #[serde(rename = "unsubscribe")]
    Unsubscribe {
        min_score: i32,
        max_score: i32,
    },
    #[serde(rename = "waitForDoc")]
    WaitForDoc {
        doc_id: u32,
        query_id: u32,
    },
    #[serde(rename = "rank")]
    Rank { score: i32 },
    #[serde(rename = "rangeCount")]
    RangeCount { min: i32, max: i32 },
}

#[derive(Debug, Serialize)]
#[serde(tag = "type")]
enum ServerMessage {
    #[serde(rename = "connected")]
    Connected { connection_id: String },
    #[serde(rename = "subscribed")]
    Subscribed {
        query_id: u32,
        initial_count: u32,
    },
    #[serde(rename = "added")]
    Added {
        query_id: u32,
        id: String,
        score: i32,
    },
    #[serde(rename = "updated")]
    Updated {
        query_id: u32,
        id: String,
        score: i32,
    },
    #[serde(rename = "removed")]
    Removed { query_id: u32, id: String },
    #[serde(rename = "waitRegistered")]
    WaitRegistered { doc_id: u32, query_id: u32, batch: String },
    #[serde(rename = "rankResult")]
    RankResult { score: i32, count: u32 },
    #[serde(rename = "rangeCountResult")]
    RangeCountResult { min: i32, max: i32, count: u32 },
}

pub async fn start_websocket_server(
    addr: &str,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    pool: Arc<deadpool_postgres::Pool>,
    registry: Arc<ConnectionRegistry>,
    retrieval_jobs: Arc<RetrievalJobIndex>,
    doc_index: Arc<RwLock<DocIndex>>,
) {
    let listener = TcpListener::bind(addr).await.expect("Failed to bind");
    info!("WebSocket server listening on {}", addr);

    while let Ok((stream, peer)) = listener.accept().await {
        info!("New connection from: {}", peer);
        let range_index = range_index.clone();
        let storage = storage.clone();
        let pool = pool.clone();
    let registry = registry.clone();
    let retrieval_jobs = retrieval_jobs.clone();
    let doc_index = doc_index.clone();

        tokio::spawn(async move {
            if let Err(e) = handle_connection(stream, range_index, storage, pool, registry, retrieval_jobs, doc_index).await {
                error!("Error handling connection: {}", e);
            }
        });
    }
}

async fn handle_connection(
    stream: TcpStream,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    pool: Arc<deadpool_postgres::Pool>,
    registry: Arc<ConnectionRegistry>,
    retrieval_jobs: Arc<RetrievalJobIndex>,
    doc_index: Arc<RwLock<DocIndex>>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let ws_stream = accept_async(stream).await?;
    let (ws_sender, mut ws_receiver) = ws_stream.split();

    // Generate connection ID
    let connection_id = Uuid::new_v4().to_string();
    info!("Connection established: {}", connection_id);

    // Create notification channel for outgoing messages
    let (tx, mut rx) = mpsc::unbounded_channel::<String>();
    
    // Register connection in registry
    let (notif_tx, mut notif_rx) = mpsc::unbounded_channel();
    registry.register(connection_id.clone(), notif_tx).await;

    // Send connection ID
    let msg = ServerMessage::Connected {
        connection_id: connection_id.clone(),
    };
    let _ = tx.send(serde_json::to_string(&msg)?);

    // Spawn task to send messages to WebSocket
    let connection_id_clone = connection_id.clone();
    tokio::spawn(async move {
        let mut ws_sender = ws_sender;
        loop {
            tokio::select! {
                // Forward notifications from replication events
                Some(notification) = notif_rx.recv() => {
                    if let Ok(json) = serde_json::to_string(&notification) {
                        if ws_sender.send(Message::Text(json)).await.is_err() {
                            break;
                        }
                    }
                }
                // Forward other messages (subscribe responses, etc)
                Some(msg) = rx.recv() => {
                    if ws_sender.send(Message::Text(msg)).await.is_err() {
                        break;
                    }
                }
                else => break,
            }
        }
        info!("Sender task ended for {}", connection_id_clone);
    });

    // Handle messages
    while let Some(msg) = ws_receiver.next().await {
        match msg {
            Ok(Message::Text(text)) => {
                if let Ok(client_msg) = serde_json::from_str::<ClientMessage>(&text) {
                    match client_msg {
                        ClientMessage::Subscribe {
                            min_score,
                            max_score,
                        } => {
                            handle_subscribe(
                                &connection_id,
                                min_score,
                                max_score,
                                &range_index,
                                &storage,
                                &pool,
                                &tx,
                            )
                            .await?;
                        }
                        ClientMessage::Unsubscribe { min_score, max_score } => {
                            handle_unsubscribe(&connection_id, min_score, max_score, &range_index, &storage).await?;
                        }
                        ClientMessage::WaitForDoc { doc_id, query_id } => {
                            retrieval_jobs.register(doc_id, query_id).await;
                            let response = ServerMessage::WaitRegistered { doc_id, query_id, batch: "registration".to_string() };
                            tx.send(serde_json::to_string(&response)?)?;
                        }
                        ClientMessage::Rank { score } => {
                            let count = {
                                let di = doc_index.read().await;
                                di.rank(score)
                            };
                            let response = ServerMessage::RankResult { score, count };
                            tx.send(serde_json::to_string(&response)?)?;
                        }
                        ClientMessage::RangeCount { min, max } => {
                            let count = {
                                let di = doc_index.read().await;
                                di.range_count(min, max)
                            };
                            let response = ServerMessage::RangeCountResult { min, max, count };
                            tx.send(serde_json::to_string(&response)?)?;
                        }
                    }
                } else {
                    warn!("Failed to parse message: {}", text);
                }
            }
            Ok(Message::Close(_)) => {
                info!("Client closed connection: {}", connection_id);
                break;
            }
            Err(e) => {
                warn!("WebSocket error: {}", e);
                break;
            }
            _ => {}
        }
    }

    // Cleanup on disconnect
    registry.unregister(&connection_id).await;
    {
        let mut index = range_index.write().await;
        let queries = index.get_queries_for_connection(&connection_id);
        for query_id in queries {
            index.unsubscribe_connection(&connection_id, query_id);
            if index.get_connections_for_query(query_id).is_empty() {
                index.remove_query(query_id);
            }
        }
    }

    if let Err(e) = storage.remove_connection(&connection_id) {
        error!("Failed to cleanup connection storage: {}", e);
    }

    info!("Connection closed: {}", connection_id);
    Ok(())
}

async fn handle_subscribe(
    connection_id: &str,
    min_score: i32,
    max_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    pool: &Arc<deadpool_postgres::Pool>,
    sender: &mpsc::UnboundedSender<String>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    // Generate query_id from range
    info!("Subscribe: conn={} range=[{}, {}]", connection_id, min_score, max_score);

    // Add to index and subscribe connection
    let qid = {
        let mut index = range_index.write().await;
        let internal = index.add_query(min_score as f64, i64::MAX, max_score as f64);
        index.subscribe_connection(connection_id.to_string(), internal);
        internal
    };

    // Get a connection from the pool
    let client = match pool.get().await {
        Ok(c) => c,
        Err(e) => {
            error!("Failed to get DB connection from pool: {}", e);
            return Err(format!("Database connection error: {}", e).into());
        }
    };

    // Query documents in range
    let query = "SELECT id, score FROM docs WHERE score >= $1 AND score <= $2";
    let rows = match client.query(query, &[&min_score, &max_score]).await {
        Ok(r) => r,
        Err(e) => {
            error!("Failed to query documents: {:?}", e);
            error!("Query was: {} with params [{}, {}]", query, min_score, max_score);
            return Err(format!("Database query error: {:?}", e).into());
        }
    };
    
    let initial_count = rows.len();
    
    // Apply DB results with state machine
    for row in rows {
        let doc_id: i32 = row.get(0);
        storage.apply_db_result(connection_id, qid, doc_id as u32)?;
    }

    // Send subscription acknowledgment with initial count
    let response = ServerMessage::Subscribed { query_id: qid, initial_count: initial_count as u32 };

    sender.send(serde_json::to_string(&response)?)?;

    Ok(())
}

async fn handle_unsubscribe(
    connection_id: &str,
    min_score: i32,
    max_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    info!("Unsubscribe: conn={} range=[{}, {}]", connection_id, min_score, max_score);
    let mut index = range_index.write().await;
    if let Some(qid) = index.lookup_range_query_id(min_score as f64, i64::MAX, max_score as f64) {
        index.unsubscribe_connection(connection_id, qid);
        // Cleanup LMDB entries for this (connection, query)
        let _ = storage.remove_query_for_connection(connection_id, qid);
        if index.get_connections_for_query(qid).is_empty() {
            index.remove_query(qid);
        }
    }

    Ok(())
}
