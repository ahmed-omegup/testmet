use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{accept_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use tracing::{info, error, warn};
use uuid::Uuid;
use tokio_postgres::{NoTls, Row};

use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;

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
}

#[derive(Debug, Serialize)]
#[serde(tag = "type")]
enum ServerMessage {
    #[serde(rename = "connected")]
    Connected { connection_id: String },
    #[serde(rename = "subscribed")]
    Subscribed {
        query_id: String,
        initial_count: usize,
    },
    #[serde(rename = "added")]
    Added {
        query_id: String,
        id: String,
        score: i32,
    },
    #[serde(rename = "updated")]
    Updated {
        query_id: String,
        id: String,
        score: i32,
    },
    #[serde(rename = "removed")]
    Removed { query_id: String, id: String },
}

pub async fn start_websocket_server(
    addr: &str,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
) {
    let listener = TcpListener::bind(addr).await.expect("Failed to bind");
    info!("WebSocket server listening on {}", addr);

    while let Ok((stream, peer)) = listener.accept().await {
        info!("New connection from: {}", peer);
        let range_index = range_index.clone();
        let storage = storage.clone();

        tokio::spawn(async move {
            if let Err(e) = handle_connection(stream, range_index, storage).await {
                error!("Error handling connection: {}", e);
            }
        });
    }
}

async fn handle_connection(
    stream: TcpStream,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
) -> Result<(), Box<dyn std::error::Error>> {
    let ws_stream = accept_async(stream).await?;
    let (mut ws_sender, mut ws_receiver) = ws_stream.split();

    // Generate connection ID
    let connection_id = Uuid::new_v4().to_string();
    info!("Connection established: {}", connection_id);

    // Send connection ID
    let msg = ServerMessage::Connected {
        connection_id: connection_id.clone(),
    };
    ws_sender
        .send(Message::Text(serde_json::to_string(&msg)?))
        .await?;

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
                                &mut ws_sender,
                            )
                            .await?;
                        }
                        ClientMessage::Unsubscribe { min_score, max_score } => {
                            handle_unsubscribe(&connection_id, min_score, max_score, &range_index).await?;
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
    {
        let mut index = range_index.write().await;
        let queries = index.get_queries_for_connection(&connection_id);
        for query in queries {
            index.remove_query(&query.query_id);
        }
    }

    if let Err(e) = storage.remove_connection(&connection_id) {
        error!("Failed to cleanup connection storage: {}", e);
    }

    info!("Connection closed: {}", connection_id);
    Ok(())
}

async fn handle_subscribe<S>(
    connection_id: &str,
    min_score: i32,
    max_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    ws_sender: &mut S,
) -> Result<(), Box<dyn std::error::Error>>
where
    S: SinkExt<Message> + Unpin,
    <S as futures_util::Sink<Message>>::Error: std::error::Error + Send + Sync + 'static,
{
    // Generate query_id from range
    let query_id = format!("{}:{}", min_score, max_score);
    
    info!(
        "Subscribe: conn={} query={} range=[{}, {}]",
        connection_id, query_id, min_score, max_score
    );

    // Add to index
    {
        let mut index = range_index.write().await;
        index.add_query(
            connection_id.to_string(),
            query_id.clone(),
            min_score,
            max_score,
        );
    }

    // Execute PostgreSQL query for initial data
    let pg_url = std::env::var("POSTGRES_URL")
        .unwrap_or_else(|_| "postgresql://postgres:postgres@localhost:5432/benchmark".to_string());
    
    let (client, connection) = tokio_postgres::connect(&pg_url, tokio_postgres::NoTls).await?;
    
    // Spawn connection handler
    tokio::spawn(async move {
        if let Err(e) = connection.await {
            error!("PostgreSQL connection error: {}", e);
        }
    });

    // Query documents in range
    let query = "SELECT id, score FROM documents WHERE score >= $1 AND score <= $2";
    let rows = client.query(query, &[&min_score, &max_score]).await?;
    
    let initial_count = rows.len();
    
    // Apply DB results with state machine
    for row in rows {
        let doc_id: String = row.get(0);
        storage.apply_db_result(connection_id, &query_id, &doc_id)?;
    }

    // Send subscription acknowledgment with initial count
    let response = ServerMessage::Subscribed {
        query_id,
        initial_count,
    };

    ws_sender
        .send(Message::Text(serde_json::to_string(&response)?))
        .await?;

    Ok(())
}

async fn handle_unsubscribe(
    connection_id: &str,
    min_score: i32,
    max_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Generate query_id from range
    let query_id = format!("{}:{}", min_score, max_score);
    
    info!("Unsubscribe: conn={} query={}", connection_id, query_id);

    let mut index = range_index.write().await;
    index.remove_query(&query_id);

    Ok(())
}
