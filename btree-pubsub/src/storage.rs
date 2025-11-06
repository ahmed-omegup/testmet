use heed::{Database, Env, EnvOpenOptions};
use heed::types::*;
use heed::byteorder::BigEndian;
use std::path::Path;

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

/// LMDB-based storage for subscription tracking
/// - connection_documents: connection:query:node:id -> state (i8: -1, 0, 1)
/// - document_connections: id:connection -> count (u32)
pub struct SubscriptionStore {
    env: Env,
    connection_documents: Database<Str, I8>,
    document_connections: Database<Str, U32<BigEndian>>,
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
        })
    }

    /// Add a document to a connection's subscription (insertion event: any -> 1)
    pub fn add_document_to_connection(
        &self,
        connection_id: &str,
        query_id: &str,
        doc_id: &str,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;

        // connection:query:node:id -> 1 (exists)
        let conn_key = format!("{}:{}:node:{}", connection_id, query_id, doc_id);
        let old_state = self.connection_documents.get(&wtxn, &conn_key)?;
        
        // Insertion event: any -> 1
        self.connection_documents.put(&mut wtxn, &conn_key, &(DocState::Exists as i8))?;

        // Update id:connection count if state changed from non-1 to 1
        if old_state != Some(DocState::Exists as i8) {
            let doc_key = format!("{}:{}", doc_id, connection_id);
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
        query_id: &str,
        doc_id: &str,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;

        let conn_key = format!("{}:{}:node:{}", connection_id, query_id, doc_id);
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
                    let doc_key = format!("{}:{}", doc_id, connection_id);
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
        query_id: &str,
        doc_id: &str,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;

        let conn_key = format!("{}:{}:node:{}", connection_id, query_id, doc_id);
        let old_state = self.connection_documents.get(&wtxn, &conn_key)?;

        match old_state {
            None => {
                // Not set: 0 -> 1
                self.connection_documents.put(&mut wtxn, &conn_key, &(DocState::Exists as i8))?;
                
                // Update count
                let doc_key = format!("{}:{}", doc_id, connection_id);
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
                let doc_key = format!("{}:{}", doc_id, connection_id);
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
        query_id: &str,
        doc_id: &str,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.handle_deletion(connection_id, query_id, doc_id)
    }

    /// Check if a connection already has this document
    pub fn has_document(
        &self,
        connection_id: &str,
        query_id: &str,
        doc_id: &str,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let rtxn = self.env.read_txn()?;
        let key = format!("{}:{}:node:{}", connection_id, query_id, doc_id);
        Ok(self.connection_documents.get(&rtxn, &key)?.is_some())
    }

    /// Get all connections for a document
    pub fn get_connections_for_document(&self, doc_id: &str) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        let rtxn = self.env.read_txn()?;
        let prefix = format!("{}:", doc_id);
        let mut connections = Vec::new();

        let iter = self.document_connections.prefix_iter(&rtxn, &prefix)?;
        for result in iter {
            let (key, _) = result?;
            if let Some(conn_id) = key.split(':').nth(1) {
                connections.push(conn_id.to_string());
            }
        }

        Ok(connections)
    }

    /// Get all documents for a connection query
    pub fn get_documents_for_query(
        &self,
        connection_id: &str,
        query_id: &str,
    ) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        let rtxn = self.env.read_txn()?;
        let prefix = format!("{}:{}:node:", connection_id, query_id);
        let mut documents = Vec::new();

        let iter = self.connection_documents.prefix_iter(&rtxn, &prefix)?;
        for result in iter {
            let (key, _) = result?;
            if let Some(doc_id) = key.split(':').nth(3) {
                documents.push(doc_id.to_string());
            }
        }

        Ok(documents)
    }

    /// Remove all subscriptions for a connection
    pub fn remove_connection(&self, connection_id: &str) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut wtxn = self.env.write_txn()?;
        let prefix = format!("{}:", connection_id);

        // Collect keys to remove
        let mut keys_to_remove = Vec::new();
        {
            let rtxn = self.env.read_txn()?;
            let iter = self.connection_documents.prefix_iter(&rtxn, &prefix)?;
            for result in iter {
                let (key, _) = result?;
                keys_to_remove.push(key.to_string());
            }
        }

        // Remove all entries
        for key in keys_to_remove {
            self.connection_documents.delete(&mut wtxn, &key)?;
            
            // Also update document_connections
            let parts: Vec<&str> = key.split(':').collect();
            if parts.len() >= 4 {
                let doc_id = parts[3];
                let doc_key = format!("{}:{}", doc_id, connection_id);
                self.document_connections.delete(&mut wtxn, &doc_key).ok();
            }
        }

        wtxn.commit()?;
        Ok(())
    }
}
