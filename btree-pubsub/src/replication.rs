use tokio_postgres::{Client, NoTls};
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, error, warn};
use crate::btree_index::RangeQueryIndex;
use crate::storage::SubscriptionStore;
use crate::connection_registry::{ConnectionRegistry, Notification, Document, ChangeMeta};
use crate::retrieval_job::RetrievalJobIndex;
use crate::doc_index::DocIndex;
use std::collections::HashSet;
use prost::Message;

mod decoderbufs {
    include!(concat!(env!("OUT_DIR"), "/decoderbufs.rs"));
}

/// Start PostgreSQL logical replication reader
pub async fn start_replication(
    pg_url: String,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    registry: Arc<ConnectionRegistry>,
    retrieval_jobs: Arc<RetrievalJobIndex>,
    doc_index: Arc<RwLock<DocIndex>>,
) {
    if let Err(e) = run_replication(&pg_url, range_index, storage, registry, retrieval_jobs, doc_index).await {
        error!("Fatal replication error: {}", e);
        std::process::exit(1);
    }
}

async fn run_replication(
    pg_url: &str,
    range_index: Arc<RwLock<RangeQueryIndex>>,
    storage: Arc<SubscriptionStore>,
    registry: Arc<ConnectionRegistry>,
    retrieval_jobs: Arc<RetrievalJobIndex>,
    doc_index: Arc<RwLock<DocIndex>>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let (client, connection) = tokio_postgres::connect(pg_url, NoTls).await?;
    tokio::spawn(async move {
        if let Err(e) = connection.await {
            error!("PostgreSQL connection error: {}", e);
        }
    });

    info!("Connected to PostgreSQL for replication");
    setup_replication_slot(&client).await?;
    consume_changes(client, range_index, storage, registry, retrieval_jobs, doc_index).await?;
    Ok(())
}

async fn setup_replication_slot(client: &Client) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
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
    retrieval_jobs: Arc<RetrievalJobIndex>,
    doc_index: Arc<RwLock<DocIndex>>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    info!("Starting to consume logical replication stream...");
    let query = "SELECT lsn, xid, data FROM pg_logical_slot_get_binary_changes('btree_pubsub_slot', NULL, NULL)";
    loop {
        match client.query(query, &[]).await {
            Ok(rows) => {
                if rows.len() > 0 { info!("Received {} replication messages", rows.len()); }
                for row in rows {
                    if let Ok(data) = row.try_get::<_, Vec<u8>>(2) {
                        process_decoderbufs_message(&data, &range_index, &storage, &registry, &retrieval_jobs, &doc_index).await;
                    }
                }
                // Chain retrieval job rotation: promote registration batch only if it has entries
                retrieval_jobs.promote_if_needed().await;
            }
            Err(e) => {
                error!("Fatal error reading changes: {:?}", e);
                return Err(e.into());
            }
        }
    }
}

async fn process_decoderbufs_message(
    data: &[u8],
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
    retrieval_jobs: &Arc<RetrievalJobIndex>,
    doc_index: &Arc<RwLock<DocIndex>>,
) {
    if data.is_empty() {
        return;
    }

    // Decode protobuf message
    let row_msg = match decoderbufs::RowMessage::decode(data) {
        Ok(msg) => msg,
        Err(e) => {
            error!("Failed to decode protobuf message: {}", e);
            return;
        }
    };

    // Check operation type
    let op = row_msg.op();
    
    match op {
        decoderbufs::Op::Insert => {
            if let Some((id, score_opt, ts_opt)) = extract_id_score_ts(&row_msg.new_tuple) {
                if let Some(score) = score_opt {
                    handle_insert(id, score, ts_opt.unwrap_or(0), range_index, storage, registry, retrieval_jobs, doc_index).await;
                }
            }
        }
        decoderbufs::Op::Update => {
            let old = extract_id_score_ts(&row_msg.old_tuple);
            let newv = extract_id_score_ts(&row_msg.new_tuple);
            match (newv, old) {
                (Some((id_new, new_score_opt, new_ts_opt)), Some((_id_old, old_score_opt, _))) => {
                    if let Some(new_score) = new_score_opt {
                        handle_update(id_new.clone(), old_score_opt, new_score, range_index, storage, registry, retrieval_jobs, doc_index).await;
                    }
                    if let Some(ts) = new_ts_opt { 
                        if ts == -1 { 
                            info!("Broadcasting timestamp update for doc: {}, ts={}", id_new, ts);
                            broadcast_timestamp_update(id_new as u32, ts, range_index, registry).await; 
                        } 
                    }
                }
                (Some((id, new_score_opt, new_ts_opt)), None) => {
                    if let Some(new_score) = new_score_opt {
                        handle_update(id.clone(), None, new_score, range_index, storage, registry, retrieval_jobs, doc_index).await;
                    }
                    if let Some(ts) = new_ts_opt { if ts == -1 { broadcast_timestamp_update(id as u32, ts, range_index, registry).await; } }
                }
                _ => {}
            }
        }
        decoderbufs::Op::Delete => {
            if let Some((id, old_score_opt, _)) = extract_id_score_ts(&row_msg.old_tuple) {
                if let Some(old_score) = old_score_opt {
                    handle_delete(id, old_score, range_index, storage, registry, retrieval_jobs, doc_index).await;
                } else if let Some(id2) = extract_id(&row_msg.old_tuple) {
                    handle_delete_no_value(id2, range_index, storage, registry, retrieval_jobs, doc_index).await;
                }
            } else if let Some(id) = extract_id(&row_msg.old_tuple) {
                handle_delete_no_value(id, range_index, storage, registry, retrieval_jobs, doc_index).await;
            }
        }
        decoderbufs::Op::Begin | decoderbufs::Op::Commit => {
            // Transaction markers - ignore
        }
        _ => {
            warn!("Unknown operation type: {:?}", op);
        }
    }
}

fn extract_id_score_ts(tuple: &[decoderbufs::DatumMessage]) -> Option<(u32, Option<i32>, Option<i32>)> {
    let mut id: Option<u32> = None;
    let mut score: Option<i32> = None;
    let mut timestamp: Option<i32> = None;

    for datum in tuple {
        let col_name = datum.column_name.as_ref()?;
        
        match col_name.as_str() {
            "id" => {
                if let Some(decoderbufs::datum_message::Datum::DatumInt64(v)) = datum.datum {
                    if v >= 0 && v <= u32::MAX as i64 { id = Some(v as u32); }
                } else if let Some(decoderbufs::datum_message::Datum::DatumInt32(v)) = datum.datum {
                    if v >= 0 { id = Some(v as u32); }
                }
            }
            "score" => {
                if let Some(decoderbufs::datum_message::Datum::DatumInt32(s)) = datum.datum {
                    score = Some(s);
                } else if let Some(decoderbufs::datum_message::Datum::DatumInt64(s)) = datum.datum {
                    score = Some(s as i32);
                }
            }
            "timestamp" | "\"timestamp\"" => {
                if let Some(decoderbufs::datum_message::Datum::DatumInt32(t)) = datum.datum {
                    timestamp = Some(t);
                } else if let Some(decoderbufs::datum_message::Datum::DatumInt64(t)) = datum.datum {
                    timestamp = Some(t as i32);
                }
            }
            _ => {}
        }
    }
    let result = id.map(|idv| (idv, score, timestamp));
    if let Some((ref id_val, ref score_val, ref ts_val)) = result {
        info!("Extracted: id={}, score={:?}, timestamp={:?}", id_val, score_val, ts_val);
    }
    result
}

fn extract_id(tuple: &[decoderbufs::DatumMessage]) -> Option<u32> {
    for datum in tuple {
        if let Some(ref col_name) = datum.column_name {
            if col_name == "id" {
                if let Some(decoderbufs::datum_message::Datum::DatumInt64(v)) = datum.datum { info!("Extracted DELETE id={}", v); if v>=0 && v<=u32::MAX as i64 { return Some(v as u32); } }
                if let Some(decoderbufs::datum_message::Datum::DatumInt32(v)) = datum.datum { info!("Extracted DELETE id={}", v); if v>=0 { return Some(v as u32); } }
            }
        }
    }
    None
}

async fn handle_insert(
    id: u32,
    score: i32,
    timestamp: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
    retrieval_jobs: &Arc<RetrievalJobIndex>,
    doc_index: &Arc<RwLock<DocIndex>>,
) {
    // Get queries this document matches
    let matches = {
        let mut index = range_index.write().await;
        index.get_queries_for_change(id, None, score as f64, 1)
    };
    // Collect unique connections across all affected queries and emit a single ChangeEvent
    let mut conn_set: HashSet<String> = HashSet::new();
    for query_id in &matches.added_to {
        let conns = { let index = range_index.read().await; index.get_connections_for_query(*query_id) };
        for c in conns { conn_set.insert(c); }
    }

    if !conn_set.is_empty() {
        let conns_vec: Vec<String> = conn_set.into_iter().collect();
        let new_doc = Document { id, score: Some(score), timestamp: Some(timestamp), name: None };
        let notification = Notification::ChangeEvent {
            id,
            old: None,
            new: Some(new_doc),
            added_to: matches.added_to.clone(),
            removed_from: vec![],
            meta: Some(ChangeMeta { op: "INSERT".to_string(), lsn: None }),
        };
        registry.notify_many(&conns_vec, notification).await;
    }

    // Also handle retrieval job waiting queries in processing batch
    {
        let mut di = doc_index.write().await;
        di.insert(id, score);
        let waiting_queries = retrieval_jobs.document_arrived(id).await;
        if !waiting_queries.is_empty() {
            // Gather connections subscribed to these queries
            use std::collections::HashSet;
            let mut conn_set: HashSet<String> = HashSet::new();
            for qid in &waiting_queries {
                let conns = { let index = range_index.read().await; index.get_connections_for_query(*qid) };
                for c in conns { conn_set.insert(c); }
            }
            if !conn_set.is_empty() {
                let conns_vec: Vec<String> = conn_set.into_iter().collect();
                let new_doc = Document { id, score: Some(score), timestamp: Some(timestamp), name: None };
                let notification = Notification::ChangeEvent {
                    id,
                    old: None,
                    new: Some(new_doc),
                    added_to: waiting_queries.clone(),
                    removed_from: vec![],
                    meta: Some(ChangeMeta { op: "RETRIEVAL".to_string(), lsn: None }),
                };
                registry.notify_many(&conns_vec, notification).await;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::connection_registry::ConnectionRegistry;
    use crate::storage::SubscriptionStore;
    use uuid::Uuid;
    use std::fs;
    use std::path::PathBuf;
    use tokio::time::{timeout, Duration};

    #[tokio::test]
    async fn change_event_insert_update_delete() {
        let registry = ConnectionRegistry::new();
        let range_index = Arc::new(RwLock::new(RangeQueryIndex::new(0, 1000)));
        let retrieval_jobs = Arc::new(RetrievalJobIndex::new());
        let temp_path: PathBuf = std::env::temp_dir().join(format!("store_test_{}", Uuid::new_v4()));
        fs::create_dir_all(&temp_path).unwrap();
        let store = Arc::new(SubscriptionStore::new(&temp_path).unwrap());

        // Register test connection
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel();
        let conn_id = "conn-test".to_string();
        registry.register(conn_id.clone(), tx).await;

        // Add a query covering score range 40..80
        let qid = {
            let mut idx = range_index.write().await;
            let qid = idx.add_query(40.0, 5, 80.0);
            idx.subscribe_connection(conn_id.clone(), qid);
            qid
        };

        // Rotate retrieval jobs after registering unrelated wait so processing batch non-empty
        retrieval_jobs.register(999u32, qid).await;
        retrieval_jobs.rotate().await;

        handle_insert(1u32, 50, 0, &range_index, &store, &registry, &retrieval_jobs).await;
        {
            let idx = range_index.read().await;
            let tracked = idx.get_tracked_queries_for_document(1u32);
            assert!(tracked.contains(&qid));
        }
        let first = timeout(Duration::from_millis(500), rx.recv()).await.expect("insert timeout").expect("channel closed");
        if let Notification::ChangeEvent { id, added_to, removed_from, .. } = first {
            assert_eq!(id, 1u32);
            assert!(added_to.contains(&qid));
            assert!(removed_from.is_empty());
        } else { panic!("Unexpected variant"); }

        handle_update(1u32, Some(50), 500, &range_index, &store, &registry, &retrieval_jobs).await;
        let second = timeout(Duration::from_millis(500), rx.recv()).await.expect("update timeout").expect("channel closed");
        if let Notification::ChangeEvent { added_to, removed_from, .. } = second {
            assert!(added_to.is_empty());
            assert!(!removed_from.is_empty());
        } else { panic!("Unexpected variant"); }

        handle_delete(1u32, 500, &range_index, &store, &registry, &retrieval_jobs).await;
        {
            let idx = range_index.read().await;
            let tracked = idx.get_tracked_queries_for_document(1u32);
            assert!(tracked.is_empty());
        }
    }
}

async fn handle_update(
    id: u32,
    old_score: Option<i32>,
    new_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
    _retrieval_jobs: &Arc<RetrievalJobIndex>,
    doc_index: &Arc<RwLock<DocIndex>>,
) {
    // Get queries this document was added to or removed from
    let matches = {
        let mut index = range_index.write().await;
        index.get_queries_for_change(id, old_score.map(|s| s as f64), new_score as f64, 1)
    };
    // Collect unique connections across added_to + removed_from
    let mut conn_set: HashSet<String> = HashSet::new();
    for query_id in &matches.added_to {
        let conns = { let index = range_index.read().await; index.get_connections_for_query(*query_id) };
        for c in conns { conn_set.insert(c); }
    }
    for query_id in &matches.removed_from {
        let conns = { let index = range_index.read().await; index.get_connections_for_query(*query_id) };
        for c in conns { conn_set.insert(c); }
    }

    if !conn_set.is_empty() {
        let conns_vec: Vec<String> = conn_set.into_iter().collect();
        let old_doc = old_score.map(|s| Document { id, score: Some(s), timestamp: None, name: None });
        let new_doc = Some(Document { id, score: Some(new_score), timestamp: None, name: None });
        let notification = Notification::ChangeEvent {
            id,
            old: old_doc,
            new: new_doc,
            added_to: matches.added_to.clone(),
            removed_from: matches.removed_from.clone(),
            meta: Some(ChangeMeta { op: "UPDATE".to_string(), lsn: None }),
        };
        registry.notify_many(&conns_vec, notification).await;
    }
    // Update doc index score
    {
        let mut di = doc_index.write().await;
        if let Some(old) = old_score { di.update(id, old, new_score); } else { di.insert(id, new_score); }
    }
}

async fn handle_delete(
    id: u32,
    old_score: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
    _retrieval_jobs: &Arc<RetrievalJobIndex>,
    doc_index: &Arc<RwLock<DocIndex>>,
) {
    // Remove from index and get queries it was part of
    let query_ids = {
        let mut index = range_index.write().await;
        index.remove_document(id, old_score as f64, 1)
    };
    // Collect unique connections across affected queries and emit a ChangeEvent
    let mut conn_set: HashSet<String> = HashSet::new();
    for query_id in &query_ids {
        let conns = { let index = range_index.read().await; index.get_connections_for_query(*query_id) };
        for c in conns { conn_set.insert(c); }
    }

    if !conn_set.is_empty() {
        let conns_vec: Vec<String> = conn_set.into_iter().collect();
        let old_doc = Some(Document { id, score: Some(old_score), timestamp: None, name: None });
        let notification = Notification::ChangeEvent {
            id,
            old: old_doc,
            new: None,
            added_to: vec![],
            removed_from: query_ids.clone(),
            meta: Some(ChangeMeta { op: "DELETE".to_string(), lsn: None }),
        };
        registry.notify_many(&conns_vec, notification).await;
    }
    {
        let mut di = doc_index.write().await; di.delete(id, old_score);
    }
}

async fn handle_delete_no_value(
    id: u32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    _storage: &Arc<SubscriptionStore>,
    registry: &Arc<ConnectionRegistry>,
    _retrieval_jobs: &Arc<RetrievalJobIndex>,
    doc_index: &Arc<RwLock<DocIndex>>,
) {
    let query_ids = {
        let index = range_index.read().await;
        index.get_tracked_queries_for_document(id)
    };
    let mut conn_set: HashSet<String> = HashSet::new();
    for query_id in &query_ids {
        let conns = { let index = range_index.read().await; index.get_connections_for_query(*query_id) };
        for c in conns { conn_set.insert(c); }
    }
    if !conn_set.is_empty() {
        let conns_vec: Vec<String> = conn_set.into_iter().collect();
        let old_doc = Some(Document { id, score: None, timestamp: None, name: None });
        let notification = Notification::ChangeEvent {
            id,
            old: old_doc,
            new: None,
            added_to: vec![],
            removed_from: query_ids.clone(),
            meta: Some(ChangeMeta { op: "DELETE".to_string(), lsn: None }),
        };
        registry.notify_many(&conns_vec, notification).await;
    }
    {
        let mut di = doc_index.write().await; di.delete(id, 0);
    }
}

async fn broadcast_timestamp_update(
    id: u32,
    timestamp: i32,
    range_index: &Arc<RwLock<RangeQueryIndex>>,
    registry: &Arc<ConnectionRegistry>,
) {
    let query_ids = {
        let index = range_index.read().await;
        index.get_tracked_queries_for_document(id)
    };
    for query_id in query_ids {
        let conns = { let index = range_index.read().await; index.get_connections_for_query(query_id) };
        for conn_id in conns {
            let notification = Notification::Updated { query_id, id, score: 0, timestamp };
            registry.notify(&conn_id, notification).await;
        }
    }
}
