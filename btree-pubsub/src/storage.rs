use heed::{Database, Env, EnvOpenOptions};
use heed::types::*;
use heed::byteorder::BigEndian;
use std::path::Path;

/// LMDB-based storage for subscription tracking
/// - connection_documents: connection:query:id -> exists
/// - document_connections: id:connection -> count
pub struct SubscriptionStore {
    env: Env,
    connection_documents: Database<Str, U8>,
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

    /// Add a document to a connection's subscription
    pub fn add_document_to_connection(
        &self,
        connection_id: &str,
        query_id: &str,
        doc_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut wtxn = self.env.write_txn()?;

        // connection:query:id -> exists
        let conn_key = format!("{}:{}:{}", connection_id, query_id, doc_id);
        self.connection_documents.put(&mut wtxn, &conn_key, &1)?;

        // id:connection -> count
        let doc_key = format!("{}:{}", doc_id, connection_id);
        let count = self.document_connections.get(&wtxn, &doc_key)?.unwrap_or(0);
        self.document_connections.put(&mut wtxn, &doc_key, &(count + 1))?;

        wtxn.commit()?;
        Ok(())
    }

    /// Remove a document from a connection's subscription
    pub fn remove_document_from_connection(
        &self,
        connection_id: &str,
        query_id: &str,
        doc_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut wtxn = self.env.write_txn()?;

        let conn_key = format!("{}:{}:{}", connection_id, query_id, doc_id);
        self.connection_documents.delete(&mut wtxn, &conn_key)?;

        let doc_key = format!("{}:{}", doc_id, connection_id);
        if let Some(count) = self.document_connections.get(&wtxn, &doc_key)? {
            if count <= 1 {
                self.document_connections.delete(&mut wtxn, &doc_key)?;
            } else {
                self.document_connections.put(&mut wtxn, &doc_key, &(count - 1))?;
            }
        }

        wtxn.commit()?;
        Ok(())
    }

    /// Check if a connection already has this document
    pub fn has_document(
        &self,
        connection_id: &str,
        query_id: &str,
        doc_id: &str,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let rtxn = self.env.read_txn()?;
        let key = format!("{}:{}:{}", connection_id, query_id, doc_id);
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
        let prefix = format!("{}:{}:", connection_id, query_id);
        let mut documents = Vec::new();

        let iter = self.connection_documents.prefix_iter(&rtxn, &prefix)?;
        for result in iter {
            let (key, _) = result?;
            if let Some(doc_id) = key.split(':').nth(2) {
                documents.push(doc_id.to_string());
            }
        }

        Ok(documents)
    }

    /// Remove all subscriptions for a connection
    pub fn remove_connection(&self, connection_id: &str) -> Result<(), Box<dyn std::error::Error>> {
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
            if parts.len() >= 3 {
                let doc_id = parts[2];
                let doc_key = format!("{}:{}", doc_id, connection_id);
                self.document_connections.delete(&mut wtxn, &doc_key).ok();
            }
        }

        wtxn.commit()?;
        Ok(())
    }
}
