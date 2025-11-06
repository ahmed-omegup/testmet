use tokio::net::{TcpListener, TcpStream};
use tokio_tungstenite::{accept_async, tungstenite::Message};
use futures_util::{StreamExt, SinkExt};
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use tracing::{info, error, warn};
use uuid::Uuid;

use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum ClientMessage {
    #[serde(rename = "subscribe")]
    Subscribe {
        query_id: String,
        min_score: i32,
        max_score: i32,
    },
    #[serde(rename = "unsubscribe")]
    Unsubscribe { query_id: String },
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
                            query_id,
                            min_score,
                            max_score,
                        } => {
                            handle_subscribe(
                                &connection_id,
                                query_id,
                                min_score,
                                max_score,
                                &range_index,
                                &storage,
                                &mut ws_sender,
                            )
                            .await?;
                        }
                        ClientMessage::Unsubscribe { query_id } => {
                            handle_unsubscribe(&connection_id, &query_id, &range_index).await?;
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
    query_id: String,
    min_score: i32,
    max_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    ws_sender: &mut S,
) -> Result<(), Box<dyn std::error::Error>>
where
    S: SinkExt<Message> + Unpin,
    <S as futures_util::Sink<Message>>::Error: std::error::Error + Send + Sync + 'static,
{
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

    // TODO: Send initial data snapshot
    // For now, just acknowledge subscription
    let response = ServerMessage::Subscribed {
        query_id,
        initial_count: 0,
    };

    ws_sender
        .send(Message::Text(serde_json::to_string(&response)?))
        .await?;

    Ok(())
}

async fn handle_unsubscribe(
    connection_id: &str,
    query_id: &str,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Unsubscribe: conn={} query={}", connection_id, query_id);

    let mut index = range_index.write().await;
    index.remove_query(query_id);

    Ok(())
}
