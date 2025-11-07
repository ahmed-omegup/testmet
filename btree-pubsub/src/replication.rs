use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, error};
use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;
use crate::connection_registry::ConnectionRegistry;

use etl::config::{BatchConfig, PgConnectionConfig, PipelineConfig, TlsConfig};
use etl::destination::{Destination, DestinationError};
use etl::pipeline::Pipeline;
use etl::store::both::memory::MemoryStore;
use etl::types::{Event, TableRow};
use async_trait::async_trait;

/// Custom destination that feeds events to our BTree PubSub system
struct BTreeDestination {
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    registry: Arc<ConnectionRegistry>,
}

impl BTreeDestination {
    fn new(
        range_index: Arc<RwLock<RangeQueryIndex>>,
        storage: Arc<SubscriptionStore>,
        registry: Arc<ConnectionRegistry>,
    ) -> Self {
        Self {
            range_index,
            storage,
            registry,
        }
    }

    async fn process_insert(&self, table_row: &TableRow) {
        // Extract id, customer_id, score from the row
        if let (Some(id), Some(customer_id), Some(score)) = (
            table_row.get_i32("id"),
            table_row.get_i32("customer_id"),
            table_row.get_f64("score"),
        ) {
            info!("Event: insert doc={} customer={} score={}", id, customer_id, score);
            // TODO: Update BTree index and notify subscribers
        }
    }

    async fn process_update(&self, table_row: &TableRow) {
        if let (Some(id), Some(customer_id), Some(score)) = (
            table_row.get_i32("id"),
            table_row.get_i32("customer_id"),
            table_row.get_f64("score"),
        ) {
            info!("Event: update doc={} customer={} score={}", id, customer_id, score);
            // TODO: Update BTree index and notify subscribers
        }
    }

    async fn process_delete(&self, table_row: &TableRow) {
        if let Some(id) = table_row.get_i32("id") {
            info!("Event: delete doc={}", id);
            // TODO: Update BTree index and notify subscribers
        }
    }
}

#[async_trait]
impl Destination for BTreeDestination {
    async fn write_events(&mut self, events: Vec<Event>) -> Result<(), DestinationError> {
        for event in events {
            match event {
                Event::Insert { table_row, .. } => {
                    self.process_insert(&table_row).await;
                }
                Event::Update { new_row, .. } => {
                    self.process_update(&new_row).await;
                }
                Event::Delete { old_row, .. } => {
                    if let Some(row) = old_row {
                        self.process_delete(&row).await;
                    }
                }
                Event::Truncate { .. } => {
                    info!("Event: truncate (ignored)");
                }
                _ => {
                    // Ignore other event types
                }
            }
        }
        Ok(())
    }
}

/// Start PostgreSQL logical replication using Supabase ETL
pub async fn start_replication(
    pg_url: String,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    registry: Arc<ConnectionRegistry>,
) {
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
    // Parse connection URL
    let url = url::Url::parse(pg_url)?;
    
    let pg = PgConnectionConfig {
        host: url.host_str().unwrap_or("localhost").to_string(),
        port: url.port().unwrap_or(5432),
        name: url.path().trim_start_matches('/').to_string(),
        username: url.username().to_string(),
        password: url.password().map(|s| s.to_string()),
        tls: TlsConfig {
            enabled: false,
            trusted_root_certs: String::new(),
        },
    };

    info!("Starting Supabase ETL pipeline");

    let store = MemoryStore::new();
    let destination = BTreeDestination::new(range_index, storage, registry);

    let config = PipelineConfig {
        id: 1,
        publication_name: "electric_publication_default".to_string(),
        pg_connection: pg,
        batch: BatchConfig {
            max_size: 1000,
            max_fill_ms: 100,
        },
        table_error_retry_delay_ms: 10_000,
        table_error_retry_max_attempts: 5,
        max_table_sync_workers: 4,
    };

    let mut pipeline = Pipeline::new(config, store, destination);
    pipeline.start().await?;
    pipeline.wait().await?;

    Ok(())
}
