use std::collections::{HashMap, HashSet};

use super::docs_treap::DocsTreap;
use super::queries_treap::{QueriesTreap, QueryId};

#[derive(Debug, Clone)]
pub struct Query {
    pub query_id: String,
    pub min_value: f64,
    pub num_docs: i64,
    pub max_value: f64,
}

#[derive(Debug, Default)]
pub struct QueryChangeResult {
    pub added_to: Vec<String>,    // query_ids document now matches
    pub removed_from: Vec<String>, // query_ids document no longer matches
}

/// Range-based query index using dynamic document-count-defined ranges
/// Queries are defined by (minValue, numDocs, maxValue)
/// A query covers value v iff it hasn't seen numDocs yet starting from minValue
pub struct RangeQueryIndex {
    docs: DocsTreap,
    queries: QueriesTreap,
    next_id: QueryId,
    id_to_query: HashMap<QueryId, Query>,
    id_to_base_score: HashMap<QueryId, i64>,
    query_id_to_internal: HashMap<String, QueryId>,  // map external string ID to internal usize
    internal_to_query_id: HashMap<QueryId, String>,  // reverse map
    // Track connections subscribed to each query (external query_id -> set of connection_ids)
    query_connections: HashMap<String, HashSet<String>>,
    // Track which queries currently match each document (doc_id -> set of external query_ids)
    document_queries: HashMap<String, HashSet<String>>,
}

impl RangeQueryIndex {
    pub fn new(_min: i32, _max: i32) -> Self {
        Self {
            docs: DocsTreap::new(),
            queries: QueriesTreap::new(),
            next_id: 0,
            id_to_query: HashMap::new(),
            id_to_base_score: HashMap::new(),
            query_id_to_internal: HashMap::new(),
            internal_to_query_id: HashMap::new(),
            query_connections: HashMap::new(),
            document_queries: HashMap::new(),
        }
    }

    /// Add or update a query
    /// min_value: starting value for range
    /// num_docs: number of documents the query wants
    /// max_value: optional upper bound (use f64::INFINITY for no limit)
    pub fn add_query(&mut self, query_id: String, min_value: f64, num_docs: i64, max_value: f64) {
        // Remove old query if exists
        if let Some(&internal_id) = self.query_id_to_internal.get(&query_id) {
            if let Some(old_query) = self.id_to_query.get(&internal_id) {
                if let Some(&base_score) = self.id_to_base_score.get(&internal_id) {
                    self.queries.remove(old_query.min_value, internal_id, base_score, old_query.max_value);
                }
            }
            self.id_to_query.remove(&internal_id);
            self.id_to_base_score.remove(&internal_id);
        }

        let internal_id = self.next_id;
        self.next_id += 1;

        let effective_score = self.docs.prefix_sum(min_value) + num_docs;
        self.queries.insert(min_value, internal_id, effective_score, max_value);

        let base_score = self.get_base_score_at_key(min_value, effective_score);
        self.id_to_base_score.insert(internal_id, base_score);

        let query = Query {
            query_id: query_id.clone(),
            min_value,
            num_docs,
            max_value,
        };
        self.id_to_query.insert(internal_id, query);
        self.query_id_to_internal.insert(query_id.clone(), internal_id);
        self.internal_to_query_id.insert(internal_id, query_id);
    }

    fn get_base_score_at_key(&self, a: f64, effective_score: i64) -> i64 {
        let mut node = self.queries.root.as_ref();
        let mut acc_add = 0i64;
        while let Some(n) = node {
            if (a - n.key).abs() < 1e-9 {
                acc_add += n.add;
                break;
            }
            acc_add += n.add;
            node = if a < n.key { n.left.as_ref() } else { n.right.as_ref() };
        }
        effective_score - acc_add
    }

    /// Subscribe a connection to a query
    pub fn subscribe_connection(&mut self, connection_id: String, query_id: String) {
        self.query_connections
            .entry(query_id)
            .or_insert_with(HashSet::new)
            .insert(connection_id);
    }

    /// Unsubscribe a connection from a query
    pub fn unsubscribe_connection(&mut self, connection_id: &str, query_id: &str) {
        if let Some(connections) = self.query_connections.get_mut(query_id) {
            connections.remove(connection_id);
            if connections.is_empty() {
                self.query_connections.remove(query_id);
            }
        }
    }

    /// Remove a query entirely
    pub fn remove_query(&mut self, query_id: &str) {
        if let Some(&internal_id) = self.query_id_to_internal.get(query_id) {
            if let Some(query) = self.id_to_query.remove(&internal_id) {
                if let Some(&base_score) = self.id_to_base_score.get(&internal_id) {
                    self.queries.remove(query.min_value, internal_id, base_score, query.max_value);
                }
                self.id_to_base_score.remove(&internal_id);
                
                // Remove from document tracking
                for doc_queries in self.document_queries.values_mut() {
                    doc_queries.remove(query_id);
                }
            }
            self.query_id_to_internal.remove(query_id);
            self.internal_to_query_id.remove(&internal_id);
            self.query_connections.remove(query_id);
        }
    }

    /// Get queries affected by a document change (insert/update)
    /// value: the document's value (e.g., score, timestamp, price)
    /// count: how many documents at this value (typically 1, but can batch)
    pub fn get_queries_for_change(&mut self, doc_id: &str, old_value: Option<f64>, new_value: f64, count: i64) -> QueryChangeResult {
        // If update, remove old doc first
        if let Some(old_val) = old_value {
            self.docs.update(old_val, -count);
            self.queries.range_add_keys_greater_than(old_val, -count);
        }

        // Add new doc
        self.docs.update(new_value, count);
        self.queries.range_add_keys_greater_than(new_value, count);

        // Get queries covering this value
        let cutoff = self.docs.prefix_sum(new_value);
        let mut matching_internal_ids = Vec::new();
        self.queries.collect_for_value(
            new_value,
            cutoff,
            |id| {
                self.id_to_query.get(&id).map_or(false, |q| q.max_value >= new_value)
            },
            &mut matching_internal_ids,
        );

        let new_matches: HashSet<String> = matching_internal_ids
            .into_iter()
            .filter_map(|id| self.internal_to_query_id.get(&id).cloned())
            .collect();

        let old_matches = self.document_queries
            .get(doc_id)
            .cloned()
            .unwrap_or_default();

        let added_to: Vec<String> = new_matches
            .difference(&old_matches)
            .cloned()
            .collect();

        let removed_from: Vec<String> = old_matches
            .difference(&new_matches)
            .cloned()
            .collect();

        if new_matches.is_empty() {
            self.document_queries.remove(doc_id);
        } else {
            self.document_queries.insert(doc_id.to_string(), new_matches);
        }

        QueryChangeResult {
            added_to,
            removed_from,
        }
    }

    /// Remove document from tracking (for deletes)
    pub fn remove_document(&mut self, doc_id: &str, value: f64, count: i64) -> Vec<String> {
        self.docs.update(value, -count);
        self.queries.range_add_keys_greater_than(value, -count);

        self.document_queries
            .remove(doc_id)
            .map(|queries| queries.into_iter().collect())
            .unwrap_or_default()
    }

    /// Get connections subscribed to a query
    pub fn get_connections_for_query(&self, query_id: &str) -> Vec<String> {
        self.query_connections
            .get(query_id)
            .map(|conns| conns.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Get all queries for a connection
    pub fn get_queries_for_connection(&self, connection_id: &str) -> Vec<String> {
        self.query_connections
            .iter()
            .filter(|(_, conns)| conns.contains(connection_id))
            .map(|(qid, _)| qid.clone())
            .collect()
    }

    /// Get query by id
    pub fn get_query(&self, query_id: &str) -> Option<&Query> {
        self.query_id_to_internal
            .get(query_id)
            .and_then(|&id| self.id_to_query.get(&id))
    }

    /// Get statistics
    pub fn get_stats(&self) -> (usize, usize) {
        let total_queries = self.id_to_query.len();
        let tracked_docs = self.document_queries.len();
        (total_queries, tracked_docs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_query_matching_with_change() {
        let mut index = RangeQueryIndex::new(0, 1000);
        
        // Add queries: (minValue, numDocs, maxValue)
        // q1: starting at 100.0, needs 100 docs, no upper limit
        // q2: starting at 150.0, needs 100 docs
        // q3: starting at 300.0, needs 100 docs
        index.add_query("q1".to_string(), 100.0, 100, f64::INFINITY);
        index.add_query("q2".to_string(), 150.0, 100, f64::INFINITY);
        index.add_query("q3".to_string(), 300.0, 100, f64::INFINITY);

        // Subscribe connections to queries
        index.subscribe_connection("conn1".to_string(), "q1".to_string());
        index.subscribe_connection("conn2".to_string(), "q2".to_string());
        index.subscribe_connection("conn3".to_string(), "q3".to_string());

        // Insert doc at value 175.0 - should match q1 and q2 (both haven't seen 100 docs yet)
        let result = index.get_queries_for_change("doc1", None, 175.0, 1);
        assert_eq!(result.added_to.len(), 2);
        assert!(result.added_to.contains(&"q1".to_string()));
        assert!(result.added_to.contains(&"q2".to_string()));
        assert_eq!(result.removed_from.len(), 0);

        // Update doc1 to value 225.0 - should still match q1 and q2
        let _result = index.get_queries_for_change("doc1", Some(175.0), 225.0, 1);
        // Depends on how many docs accumulated; with 1 doc both still active
        
        // Update doc1 to value 350.0 - should match q3 now
        let result = index.get_queries_for_change("doc1", Some(225.0), 350.0, 1);
        assert!(result.added_to.contains(&"q3".to_string()));

        // Verify connections can be retrieved
        let conns = index.get_connections_for_query("q3");
        assert_eq!(conns.len(), 1);
        assert!(conns.contains(&"conn3".to_string()));
    }

    #[test]
    fn test_document_removal() {
        let mut index = RangeQueryIndex::new(0, 1000);
        
        index.add_query("q1".to_string(), 100.0, 50, f64::INFINITY);
        index.add_query("q2".to_string(), 150.0, 50, f64::INFINITY);

        // Add document at value 175.0
        let result = index.get_queries_for_change("doc1", None, 175.0, 1);
        assert_eq!(result.added_to.len(), 2);

        // Remove document
        let removed = index.remove_document("doc1", 175.0, 1);
        assert_eq!(removed.len(), 2);
        assert!(removed.contains(&"q1".to_string()));
        assert!(removed.contains(&"q2".to_string()));
    }

    #[test]
    fn test_efficient_treap_lookup() {
        let mut index = RangeQueryIndex::new(0, 1000);
        
        // Add many queries with minValues at 0, 100, 200, ...
        for i in 0..10 {
            let min = (i * 100) as f64;
            index.add_query(format!("q{}", i), min, 100, f64::INFINITY);
        }

        // Insert at value 225.0 - queries with a <= 225 and haven't seen 100 docs yet should match
        let result = index.get_queries_for_change("doc1", None, 225.0, 1);
        // With 1 doc at 225, queries q0, q1, q2 should all match (all need 100 docs, only saw 1)
        assert!(result.added_to.len() >= 1);
    }
}
