use heed::{Database, Env, EnvOpenOptions};
use heed::types::*;
use heed::types::Bytes;
use heed::byteorder::BigEndian;
use std::path::Path;
use std::sync::RwLock;
use std::collections::HashMap;

/// Document state in the state machine
/// -1: Document was deleted before DB query completed
///  0: Document exists from DB query result (not set)
///  1: Document exists (from insertion event or confirmed by DB query)
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DocState {
    Deleted = -1,
    NotSet = 0,
    Exists = 1,
}

impl From<i8> for DocState {
    fn from(val: i8) -> Self {
        match val {
            -1 => DocState::Deleted,
            0 => DocState::NotSet,
            _ => DocState::Exists,
        }
    }
}

impl From<DocState> for i8 {
    fn from(state: DocState) -> Self {
        state as i8
    }
}

/// Document metadata for replication tracking
#[derive(Debug, Clone)]
struct DocumentMetadata {
    customer_id: i32,
    score: i32,
    deleted: bool,
}

/// LMDB-based storage for subscription tracking
/// - connection_documents: connection:query:node:id -> state (i8: -1, 0, 1)
/// - document_connections: id:connection -> count (u32)
pub struct SubscriptionStore {
    env: Env,
    // Key: raw bytes encoded as described -> state (i8)
    connection_documents: Database<Bytes, I8>,
    // Key: raw bytes -> count (u32)
    document_connections: Database<Bytes, U32<BigEndian>>,
    doc_metadata: RwLock<HashMap<i32, DocumentMetadata>>,
}

impl SubscriptionStore {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        std::fs::create_dir_all(&path)?;
        
        let env = unsafe {
            EnvOpenOptions::new()
                .map_size(10 * 1024 * 1024 * 1024) // 10GB
                .max_dbs(3)
                .open(path)?
        };

        let mut wtxn = env.write_txn()?;
        let connection_documents = env.create_database(&mut wtxn, Some("connection_documents"))?;
        let document_connections = env.create_database(&mut wtxn, Some("document_connections"))?;
        wtxn.commit()?;

        Ok(Self {
            env,
            connection_documents,
            document_connections,
            doc_metadata: RwLock::new(HashMap::new()),
        })
    }

    #[inline]
    fn enc_conn_query_prefix(connection_id: &str, query_id: u32) -> Vec<u8> {
        let mut k = Vec::with_capacity(connection_id.len() + 1 + 4);
        k.extend_from_slice(connection_id.as_bytes());
        k.push(0);
        k.extend_from_slice(&query_id.to_be_bytes());
        k
    }

    #[inline]
    fn enc_conn_doc_key(connection_id: &str, query_id: u32, doc_id: u32) -> Vec<u8> {
        let mut k = Vec::with_capacity(connection_id.len() + 1 + 4 + 4);
        k.extend_from_slice(connection_id.as_bytes());
        k.push(0);
        k.extend_from_slice(&query_id.to_be_bytes());
        k.extend_from_slice(&doc_id.to_be_bytes());
        k
    }

    #[inline]
    fn enc_doc_conn_key(doc_id: u32, connection_id: &str) -> Vec<u8> {
        let mut k = Vec::with_capacity(4 + 1 + connection_id.len());
        k.extend_from_slice(&doc_id.to_be_bytes());
        k.push(0);
        k.extend_from_slice(connection_id.as_bytes());
        k
    }

    /// Remove all entries for a specific (connection, query)
    /// Decrements per-document connection counts accordingly when state was Exists (1)
    pub fn remove_query_for_connection(
        &self,
        connection_id: &str,
        query_id: u32,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;

        let prefix = Self::enc_conn_query_prefix(connection_id, query_id);

        // Collect keys and states to remove first (cannot mutate while iterating)
        let mut keys: Vec<(Vec<u8>, i8)> = Vec::new();
        {
            let rtxn = self.env.read_txn()?;
            let iter = self.connection_documents.prefix_iter(&rtxn, &prefix)?;
            for result in iter {
                let (key, state) = result?;
                keys.push((key.to_vec(), state));
            }
        }

        for (key, state) in keys {
            // key format: [conn] 0 [query BE] [doc BE]
            let doc_id = if key.len() >= 4 {
                let n = key.len();
                u32::from_be_bytes([key[n-4], key[n-3], key[n-2], key[n-1]])
            } else { 0 };

            // Remove the connection_documents entry
            self.connection_documents.delete(&mut wtxn, &key)?;

            // If it was Exists(1), decrement id:connection count
            if state == DocState::Exists as i8 {
                let doc_key = Self::enc_doc_conn_key(doc_id, connection_id);
                if let Some(count) = self.document_connections.get(&wtxn, &doc_key)? {
                    if count <= 1 {
                        self.document_connections.delete(&mut wtxn, &doc_key).ok();
                    } else {
                        self.document_connections.put(&mut wtxn, &doc_key, &(count - 1))?;
                    }
                }
            }
        }

        wtxn.commit()?;
        Ok(())
    }

    /// Add a document to a connection's subscription (insertion event: any -> 1)
    pub fn add_document_to_connection(
        &self,
        connection_id: &str,
        query_id: u32,
        doc_id: u32,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;

        // key -> 1 (exists)
        let conn_key = Self::enc_conn_doc_key(connection_id, query_id, doc_id);
        let old_state = self.connection_documents.get(&wtxn, &conn_key)?;
        
        // Insertion event: any -> 1
        self.connection_documents.put(&mut wtxn, &conn_key, &(DocState::Exists as i8))?;

        // Update id:connection count if state changed from non-1 to 1
        if old_state != Some(DocState::Exists as i8) {
            let doc_key = Self::enc_doc_conn_key(doc_id, connection_id);
            let count = self.document_connections.get(&wtxn, &doc_key)?.unwrap_or(0);
            self.document_connections.put(&mut wtxn, &doc_key, &(count + 1))?;
        }

        wtxn.commit()?;
        Ok(())
    }

    /// Handle deletion event
    pub fn handle_deletion(
        &self,
        connection_id: &str,
        query_id: u32,
        doc_id: u32,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;

        let conn_key = Self::enc_conn_doc_key(connection_id, query_id, doc_id);
        let old_state = self.connection_documents.get(&wtxn, &conn_key)?;

        match old_state {
            None => {
                // No existing key: create with -1
                self.connection_documents.put(&mut wtxn, &conn_key, &(DocState::Deleted as i8))?;
            }
            Some(state_val) => {
                // Existing key: delete it
                self.connection_documents.delete(&mut wtxn, &conn_key)?;
                
                // Update count if it was in Exists state
                if state_val == DocState::Exists as i8 {
                    let doc_key = Self::enc_doc_conn_key(doc_id, connection_id);
                    if let Some(count) = self.document_connections.get(&wtxn, &doc_key)? {
                        if count <= 1 {
                            self.document_connections.delete(&mut wtxn, &doc_key)?;
                        } else {
                            self.document_connections.put(&mut wtxn, &doc_key, &(count - 1))?;
                        }
                    }
                }
            }
        }

        wtxn.commit()?;
        Ok(())
    }

    /// Apply DB query result for a document
    /// State transitions: -1 -> 0, 0 -> 1, 1 -> 1
    pub fn apply_db_result(
        &self,
        connection_id: &str,
        query_id: u32,
        doc_id: u32,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;

        let conn_key = Self::enc_conn_doc_key(connection_id, query_id, doc_id);
        let old_state = self.connection_documents.get(&wtxn, &conn_key)?;

        match old_state {
            None => {
                // Not set: 0 -> 1
                self.connection_documents.put(&mut wtxn, &conn_key, &(DocState::Exists as i8))?;
                
                // Update count
                let doc_key = Self::enc_doc_conn_key(doc_id, connection_id);
                let count = self.document_connections.get(&wtxn, &doc_key)?.unwrap_or(0);
                self.document_connections.put(&mut wtxn, &doc_key, &(count + 1))?;
            }
            Some(state_val) if state_val == DocState::Deleted as i8 => {
                // -1 -> 0 (ignore, was deleted)
                self.connection_documents.put(&mut wtxn, &conn_key, &(DocState::NotSet as i8))?;
            }
            Some(state_val) if state_val == DocState::NotSet as i8 => {
                // 0 -> 1
                self.connection_documents.put(&mut wtxn, &conn_key, &(DocState::Exists as i8))?;
                
                // Update count
                let doc_key = Self::enc_doc_conn_key(doc_id, connection_id);
                let count = self.document_connections.get(&wtxn, &doc_key)?.unwrap_or(0);
                self.document_connections.put(&mut wtxn, &doc_key, &(count + 1))?;
            }
            Some(_) => {
                // 1 -> 1 (already exists, no change)
            }
        }

        wtxn.commit()?;
        Ok(())
    }

    /// Remove a document from a connection's subscription
    pub fn remove_document_from_connection(
        &self,
        connection_id: &str,
        query_id: u32,
        doc_id: u32,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.handle_deletion(connection_id, query_id, doc_id)
    }

    /// Check if a connection already has this document
    pub fn has_document(
        &self,
        connection_id: &str,
        query_id: u32,
        doc_id: u32,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let rtxn = self.env.read_txn()?;
        let key = Self::enc_conn_doc_key(connection_id, query_id, doc_id);
        Ok(self.connection_documents.get(&rtxn, &key)?.is_some())
    }

    /// Get all connections for a document
    pub fn get_connections_for_document(&self, doc_id: u32) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        let rtxn = self.env.read_txn()?;
        let mut prefix = Vec::with_capacity(5);
        prefix.extend_from_slice(&doc_id.to_be_bytes());
        prefix.push(0);
        let mut connections = Vec::new();

        let iter = self.document_connections.prefix_iter(&rtxn, &prefix)?;
        for result in iter {
            let (key, _) = result?;
            if key.len() > 5 {
                let conn_id = String::from_utf8_lossy(&key[5..]).into_owned();
                connections.push(conn_id);
            }
        }

        Ok(connections)
    }

    /// Get all documents for a connection query
    pub fn get_documents_for_query(
        &self,
        connection_id: &str,
        query_id: u32,
    ) -> Result<Vec<u32>, Box<dyn std::error::Error>> {
        let rtxn = self.env.read_txn()?;
        let prefix = Self::enc_conn_query_prefix(connection_id, query_id);
        let mut documents = Vec::new();

        let iter = self.connection_documents.prefix_iter(&rtxn, &prefix)?;
        for result in iter {
            let (key, _) = result?;
            if key.len() >= prefix.len() + 4 {
                let n = key.len();
                let doc_id = u32::from_be_bytes([key[n-4], key[n-3], key[n-2], key[n-1]]);
                documents.push(doc_id);
            }
        }

        Ok(documents)
    }

    /// Remove all subscriptions for a connection
    pub fn remove_connection(&self, connection_id: &str) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;
        let mut prefix = Vec::with_capacity(connection_id.len() + 1);
        prefix.extend_from_slice(connection_id.as_bytes());
        prefix.push(0);

        // Collect keys to remove
        let mut keys_to_remove: Vec<Vec<u8>> = Vec::new();
        {
            let rtxn = self.env.read_txn()?;
            let iter = self.connection_documents.prefix_iter(&rtxn, &prefix)?;
            for result in iter {
                let (key, _) = result?;
                keys_to_remove.push(key.to_vec());
            }
        }

        // Remove all entries
        for key in keys_to_remove {
            // Also update document_connections if state was Exists
            if let Some(state_val) = self.connection_documents.get(&wtxn, &key)? {
                if state_val == DocState::Exists as i8 {
                    if key.len() >= 4 {
                        let n = key.len();
                        let doc_id = u32::from_be_bytes([key[n-4], key[n-3], key[n-2], key[n-1]]);
                        let doc_key = Self::enc_doc_conn_key(doc_id, connection_id);
                        if let Some(count) = self.document_connections.get(&wtxn, &doc_key)? {
                            if count <= 1 {
                                self.document_connections.delete(&mut wtxn, &doc_key).ok();
                            } else {
                                self.document_connections.put(&mut wtxn, &doc_key, &(count - 1))?;
                            }
                        }
                    }
                }
            }
            self.connection_documents.delete(&mut wtxn, &key)?;
        }

        wtxn.commit()?;
        Ok(())
    }

    /// Track document metadata from replication events
    pub fn track_document(&self, id: i32, customer_id: i32, score: i32) {
        let mut metadata = self.doc_metadata.write().unwrap();
        metadata.insert(id, DocumentMetadata {
            customer_id,
            score,
            deleted: false,
        });
    }

    /// Get score for a document
    pub fn get_score(&self, id: i32) -> Option<i32> {
        let metadata = self.doc_metadata.read().unwrap();
        metadata.get(&id).map(|m| m.score)
    }

    /// Get customer_id for a document
    pub fn get_customer_id(&self, id: i32) -> Option<i32> {
        let metadata = self.doc_metadata.read().unwrap();
        metadata.get(&id).map(|m| m.customer_id)
    }

    /// Mark a document as deleted
    pub fn mark_deleted(&self, id: i32) {
        let mut metadata = self.doc_metadata.write().unwrap();
        if let Some(doc) = metadata.get_mut(&id) {
            doc.deleted = true;
        }
    }
}
