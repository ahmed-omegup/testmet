# Change Events Specification

## 1. Purpose
Define a canonical payload for document-level changes derived from logical replication (new_tuple / old_tuple) enabling clients to react to query membership transitions.

## 2. Payload Shape
```jsonc
{
  "id": "doc_123",            // string identifier
  "old": {                     // null on insert
    "id": "doc_123",
    "score": 42,               // index field (numeric)
    "timestamp": 17,           // replication timestamp / logical ordering
    "name": "doc_123"         // optional extra fields
  },
  "new": {                     // null on delete
    "id": "doc_123",
    "score": 47,
    "timestamp": 18,
    "name": "doc_123"
  },
  "addedToQueries": ["qA", "qC"],      // matches(new) − matches(old)
  "removedFromQueries": ["qB"],         // matches(old) − matches(new)
  "meta": {                      // MAY: optional envelope additions
    "op": "UPDATE",            // INSERT | UPDATE | DELETE
    "lsn": "<wal-position>"     // MAY: future include
  }
}
```

## 3. Semantics
| Operation | old           | new           | addedToQueries                | removedFromQueries              |
|-----------|---------------|---------------|-------------------------------|---------------------------------|
| INSERT    | null          | Document(new) | all queries matching new      | []                              |
| DELETE    | Document(old) | null          | []                            | all queries matching old        |
| UPDATE    | Document(old) | Document(new) | queries: match(new) not old   | queries: match(old) not new     |

Intersection is explicitly excluded.

## 4. Document Extraction Rules
- Missing columns in decoderbufs message → field omitted / None.
- Numeric fields coerced to i32/f64 as per index requirements.
- Quoted column names (e.g., "timestamp") normalized by stripping surrounding quotes.

## 5. Ordering / Consistency
- Emission order follows logical replication fetch order.
- For UPDATE with identical score but other field changes: old.score == new.score still processed; membership may stay the same → both arrays empty.
- Idempotency: Consumers may safely ignore events where both arrays are empty if only non-index fields changed.

## 6. Error Handling
| Case | Handling |
|------|----------|
| Decode failure | Log error; skip event (MUST not panic) |
| Missing id | Skip event (MUST) |
| Score unparsable | Treat score=None; exclude from range matching (MUST) |

## 7. Extension Points
- meta.lsn for WAL position tracking
- meta.transaction_id for batching correlation
- addedToQueriesDetailed: MAY include min/max scores of queries for debugging

## 8. Versioning
- Initial version: v1 (implicit). Future breaking changes require `"version": 2` field.

## 9. Performance Considerations
- Filter queries using existing RangeQueryIndex for both old/new score values once; reuse sets to diff.
- MUST avoid duplicate membership computation.

## 10. Open Questions (Track in decisions.md when resolved)
- Multi-field range queries (score + timestamp?)
- Aggregation changes (count-based triggers)

## 11. References
- decisions.md: D002 (full Document), D003 (exclude intersection)
