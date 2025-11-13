mod btree_index;
mod storage;
mod replication;
mod websocket;
mod connection_registry;
mod retrieval_job;

use btree_index::RangeQueryIndex;
use storage::SubscriptionStore;
use replication::start_replication;
use websocket::start_websocket_server;
use connection_registry::ConnectionRegistry;
use retrieval_job::RetrievalJobIndex;

use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::info;
use tracing_subscriber;
use deadpool_postgres::{Config, Runtime, ManagerConfig, RecyclingMethod};

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
    let registry = ConnectionRegistry::new();
    let retrieval_jobs = Arc::new(RetrievalJobIndex::new());

    // PostgreSQL connection pool
    let pg_url = std::env::var("POSTGRES_URL")
        .unwrap_or_else(|_| "postgresql://postgres:postgres@localhost:5432/benchmark".to_string());
    
    let mut cfg = Config::new();
    cfg.url = Some(pg_url.clone());
    cfg.manager = Some(ManagerConfig { recycling_method: RecyclingMethod::Fast });
    let pool = cfg.create_pool(Some(Runtime::Tokio1), tokio_postgres::NoTls)?;
    let pool = Arc::new(pool);

    info!("PostgreSQL connection pool created");

    // Start PostgreSQL logical replication reader
    let replication_handle = tokio::spawn(start_replication(
        pg_url.clone(),
        range_index.clone(),
        storage.clone(),
        registry.clone(),
        retrieval_jobs.clone(),
    ));

    // Start WebSocket server for client connections
    let ws_handle = tokio::spawn(start_websocket_server(
        "0.0.0.0:8080",
        range_index.clone(),
        storage.clone(),
        pool.clone(),
        registry.clone(),
        retrieval_jobs.clone(),
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
