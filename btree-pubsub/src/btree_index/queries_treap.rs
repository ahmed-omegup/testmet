use std::collections::{HashMap, HashSet};
use rand::Rng;

// Public numeric query identifier type (u32 sufficient per requirement)
pub type QueryId = u32;

pub struct QueriesNode {
    pub key: f64,           // minValue (a)
    pub prio: f64,
    pub add: i64,           // lazy add for entire subtree
    pub local_scores: Vec<i64>,  // sorted ascending base scores
    pub items_by_score: HashMap<i64, HashSet<QueryId>>,
    pub base_local_max: Option<i64>,
    pub subtree_max: Option<i64>,
    pub local_max_cap: f64,
    pub subtree_max_cap: f64,
    pub local_max_freq: HashMap<u64, usize>,  // map float bits to count
    pub left: Option<Box<QueriesNode>>,
    pub right: Option<Box<QueriesNode>>,
}

impl QueriesNode {
    pub fn new(key: f64) -> Self {
        Self {
            key,
            prio: rand::thread_rng().gen(),
            add: 0,
            local_scores: Vec::new(),
            items_by_score: HashMap::new(),
            base_local_max: None,
            subtree_max: None,
            local_max_cap: f64::NEG_INFINITY,
            subtree_max_cap: f64::NEG_INFINITY,
            local_max_freq: HashMap::new(),
            left: None,
            right: None,
        }
    }
}

pub struct QueriesTreap {
    pub root: Option<Box<QueriesNode>>,
}

impl QueriesTreap {
    pub fn new() -> Self {
        Self { root: None }
    }

    fn get_subtree_max(node: &Option<Box<QueriesNode>>) -> Option<i64> {
        node.as_ref().and_then(|n| n.subtree_max)
    }

    fn get_subtree_cap(node: &Option<Box<QueriesNode>>) -> f64 {
        node.as_ref().map_or(f64::NEG_INFINITY, |n| n.subtree_max_cap)
    }

    fn max_opt(a: Option<i64>, b: Option<i64>) -> Option<i64> {
        match (a, b) {
            (None, None) => None,
            (Some(x), None) | (None, Some(x)) => Some(x),
            (Some(x), Some(y)) => Some(x.max(y)),
        }
    }

    fn pull(node: &mut QueriesNode) {
        let left_max = Self::get_subtree_max(&node.left);
        let right_max = Self::get_subtree_max(&node.right);
        let local = node.base_local_max;
        let mx = Self::max_opt(local, Self::max_opt(left_max, right_max));
        node.subtree_max = mx.map(|m| node.add + m);

        let left_cap = Self::get_subtree_cap(&node.left);
        let right_cap = Self::get_subtree_cap(&node.right);
        node.subtree_max_cap = node.local_max_cap.max(left_cap).max(right_cap);
    }

    fn rotate_right(mut p: Box<QueriesNode>) -> Box<QueriesNode> {
        let mut q = p.left.take().unwrap();
        p.left = q.right.take();
        Self::pull(&mut p);
        q.right = Some(p);
        Self::pull(&mut q);
        q
    }

    fn rotate_left(mut p: Box<QueriesNode>) -> Box<QueriesNode> {
        let mut q = p.right.take().unwrap();
        p.right = q.left.take();
        Self::pull(&mut p);
        q.left = Some(p);
        Self::pull(&mut q);
        q
    }

    fn upper_bound(arr: &[i64], x: i64) -> usize {
        let mut lo = 0;
        let mut hi = arr.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            if arr[mid] < x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        lo
    }

    fn insert_into_local(node: &mut QueriesNode, id: QueryId, base_score: i64, max_cap: f64) {
        let idx = Self::upper_bound(&node.local_scores, base_score);
        node.local_scores.insert(idx, base_score);
        node.items_by_score.entry(base_score).or_insert_with(HashSet::new).insert(id);
        node.base_local_max = node.local_scores.last().copied();

        let cap_bits = max_cap.to_bits();
        *node.local_max_freq.entry(cap_bits).or_insert(0) += 1;
        if max_cap > node.local_max_cap {
            node.local_max_cap = max_cap;
        }
    }

    fn remove_from_local(node: &mut QueriesNode, id: QueryId, base_score: i64, max_cap: f64) -> bool {
        let set = match node.items_by_score.get_mut(&base_score) {
            Some(s) => s,
            None => return false,
        };
        if !set.remove(&id) {
            return false;
        }
        if set.is_empty() {
            node.items_by_score.remove(&base_score);
        }

        if let Some(idx) = node.local_scores.iter().position(|&x| x == base_score) {
            node.local_scores.remove(idx);
        }
        node.base_local_max = node.local_scores.last().copied();

        let cap_bits = max_cap.to_bits();
        if let Some(count) = node.local_max_freq.get_mut(&cap_bits) {
            if *count <= 1 {
                node.local_max_freq.remove(&cap_bits);
                if (max_cap - node.local_max_cap).abs() < 1e-9 {
                    node.local_max_cap = node.local_max_freq.keys()
                        .map(|&bits| f64::from_bits(bits))
                        .fold(f64::NEG_INFINITY, f64::max);
                }
            } else {
                *count -= 1;
            }
        }
        true
    }

    pub fn range_add_keys_greater_than(&mut self, t: f64, delta: i64) {
        let (left, right) = Self::split_by_key(self.root.take(), t);
        let right = right.map(|mut r| {
            r.add += delta;
            if let Some(max) = r.subtree_max {
                r.subtree_max = Some(max + delta);
            }
            r
        });
        self.root = Self::merge(left, right);
    }

    pub fn insert(&mut self, a: f64, id: QueryId, effective_score: i64, max_cap: f64) {
        self.root = Self::insert_node(self.root.take(), a, id, effective_score, max_cap, 0);
    }

    fn insert_node(
        node: Option<Box<QueriesNode>>,
        a: f64,
        id: QueryId,
        effective_score: i64,
        max_cap: f64,
        acc_add: i64,
    ) -> Option<Box<QueriesNode>> {
        let mut node = match node {
            None => {
                let mut new_node = Box::new(QueriesNode::new(a));
                let base_score = effective_score - acc_add - new_node.add;
                Self::insert_into_local(&mut new_node, id, base_score, max_cap);
                Self::pull(&mut new_node);
                return Some(new_node);
            }
            Some(n) => n,
        };

        if (a - node.key).abs() < 1e-9 {
            let base_score = effective_score - acc_add - node.add;
            Self::insert_into_local(&mut node, id, base_score, max_cap);
            Self::pull(&mut node);
            return Some(node);
        }

        if a < node.key {
            node.left = Self::insert_node(node.left.take(), a, id, effective_score, max_cap, acc_add + node.add);
            if node.left.as_ref().map_or(false, |l| l.prio > node.prio) {
                return Some(Self::rotate_right(node));
            }
        } else {
            node.right = Self::insert_node(node.right.take(), a, id, effective_score, max_cap, acc_add + node.add);
            if node.right.as_ref().map_or(false, |r| r.prio > node.prio) {
                return Some(Self::rotate_left(node));
            }
        }
        Self::pull(&mut node);
        Some(node)
    }

    pub fn remove(&mut self, a: f64, id: QueryId, base_score: i64, max_cap: f64) {
        self.root = Self::remove_node(self.root.take(), a, id, base_score, max_cap);
    }

    fn remove_node(
        node: Option<Box<QueriesNode>>,
        a: f64,
        id: QueryId,
        base_score: i64,
        max_cap: f64,
    ) -> Option<Box<QueriesNode>> {
        let mut node = node?;

        if (a - node.key).abs() < 1e-9 {
            Self::remove_from_local(&mut node, id, base_score, max_cap);
        } else if a < node.key {
            node.left = Self::remove_node(node.left.take(), a, id, base_score, max_cap);
        } else {
            node.right = Self::remove_node(node.right.take(), a, id, base_score, max_cap);
        }

        if node.base_local_max.is_none() && node.left.is_none() && node.right.is_none() {
            return None;
        }

        Self::pull(&mut node);
        Some(node)
    }

    pub fn collect_for_value<F>(&mut self, v: f64, cutoff: i64, mut is_allowed: F, result: &mut Vec<QueryId>)
    where
        F: FnMut(QueryId) -> bool,
    {
        let (left, right) = Self::split_by_key(self.root.take(), v);
        Self::collect(left.as_ref(), 0, cutoff, v, &mut is_allowed, result);
        self.root = Self::merge(left, right);
    }

    fn collect<F>(
        node: Option<&Box<QueriesNode>>,
        acc_add: i64,
        cutoff: i64,
        v: f64,
        is_allowed: &mut F,
        result: &mut Vec<QueryId>,
    )
    where
        F: FnMut(QueryId) -> bool,
    {
        let node = match node {
            Some(n) => n,
            None => return,
        };

        if node.subtree_max_cap < v {
            return;
        }

        let eff_sub_max = node.subtree_max.map(|m| m + acc_add);
        if eff_sub_max.map_or(true, |m| m <= cutoff) {
            return;
        }

        let acc_here = acc_add + node.add;
        let threshold_base = cutoff - acc_here;

        if !node.local_scores.is_empty() {
            let idx = Self::upper_bound(&node.local_scores, threshold_base + 1);
            for &base in &node.local_scores[idx..] {
                if let Some(set) = node.items_by_score.get(&base) {
                    for &id in set {
                        if is_allowed(id) {
                            result.push(id);
                        }
                    }
                }
            }
        }

        Self::collect(node.left.as_ref(), acc_here, cutoff, v, is_allowed, result);
        Self::collect(node.right.as_ref(), acc_here, cutoff, v, is_allowed, result);
    }

    fn split_by_key(
        node: Option<Box<QueriesNode>>,
        key: f64,
    ) -> (Option<Box<QueriesNode>>, Option<Box<QueriesNode>>) {
        let mut node = match node {
            None => return (None, None),
            Some(n) => n,
        };

        if key < node.key {
            let (l1, l2) = Self::split_by_key(node.left.take(), key);
            node.left = l2;
            Self::pull(&mut node);
            (l1, Some(node))
        } else {
            let (r1, r2) = Self::split_by_key(node.right.take(), key);
            node.right = r1;
            Self::pull(&mut node);
            (Some(node), r2)
        }
    }

    fn merge(
        a: Option<Box<QueriesNode>>,
        b: Option<Box<QueriesNode>>,
    ) -> Option<Box<QueriesNode>> {
        match (a, b) {
            (None, None) => None,
            (Some(x), None) | (None, Some(x)) => Some(x),
            (Some(mut a), Some(mut b)) => {
                if a.prio > b.prio {
                    a.right = Self::merge(a.right.take(), Some(b));
                    Self::pull(&mut a);
                    Some(a)
                } else {
                    b.left = Self::merge(Some(a), b.left.take());
                    Self::pull(&mut b);
                    Some(b)
                }
            }
        }
    }
}
