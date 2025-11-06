mod btree_index;
mod storage;
mod replication;
mod websocket;

use btree_index::RangeQueryIndex;
use storage::SubscriptionStore;
use replication::start_replication;
use websocket::start_websocket_server;

use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::info;
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing - respects RUST_LOG environment variable
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "btree_pubsub=info,tokio_postgres::connection=warn".into())
        )
        .init();

    info!("Starting B-Tree PubSub Server");

    // Initialize data structures
    let range_index = Arc::new(RwLock::new(RangeQueryIndex::new(0, 1000)));
    let storage = Arc::new(SubscriptionStore::new("./data")?);

    // PostgreSQL connection string
    let pg_url = std::env::var("POSTGRES_URL")
        .unwrap_or_else(|_| "postgresql://postgres:postgres@localhost:5432/benchmark".to_string());

    // Start PostgreSQL logical replication reader
    let replication_handle = tokio::spawn(start_replication(
        pg_url.clone(),
        range_index.clone(),
        storage.clone(),
    ));

    // Start WebSocket server for client connections
    let ws_handle = tokio::spawn(start_websocket_server(
        "0.0.0.0:8080",
        range_index.clone(),
        storage.clone(),
    ));

    info!("B-Tree PubSub Server started");
    info!("WebSocket server listening on ws://0.0.0.0:8080");
    info!("PostgreSQL replication from: {}", pg_url);

    // Wait for both tasks
    tokio::select! {
        _ = replication_handle => info!("Replication stopped"),
        _ = ws_handle => info!("WebSocket server stopped"),
    }

    Ok(())
}
