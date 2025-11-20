pub type DocId = u32;
pub type QueryId = u32;
pub type Score = i64;

/// Simple scored document used by the reference index.
#[derive(Clone, Debug)]
pub struct ScoredDoc {
    pub score: Score,
}

/// Range-based query with a strict cap.
#[derive(Clone, Debug)]
pub struct RangeSpec {
    pub min_score: Score,
    pub max_score: Score,
    pub limit: usize,
}

impl RangeSpec {
    pub fn contains(&self, score: Score) -> bool {
        score >= self.min_score && score <= self.max_score
    }
}
