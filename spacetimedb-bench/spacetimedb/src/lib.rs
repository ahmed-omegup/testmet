use spacetimedb::{ReducerContext, Table};

#[spacetimedb::table(accessor = doc, public)]
pub struct Doc {
    #[primary_key]
    id: u64,
    #[index(btree)]
    score: u32,
    name: String,
    timestamp: i32,
}

#[spacetimedb::reducer(init)]
pub fn init(_ctx: &ReducerContext) {}

#[spacetimedb::reducer(client_connected)]
pub fn identity_connected(_ctx: &ReducerContext) {}

#[spacetimedb::reducer(client_disconnected)]
pub fn identity_disconnected(_ctx: &ReducerContext) {}

fn assert_same_len(label: &str, left: usize, right: usize) -> Result<(), String> {
    if left != right {
        return Err(format!("{label} length mismatch: {left} != {right}"));
    }
    Ok(())
}

#[spacetimedb::reducer]
pub fn clear_all(ctx: &ReducerContext) {
    let ids: Vec<u64> = ctx.db.doc().iter().map(|doc| doc.id).collect();
    for id in ids {
        ctx.db.doc().id().delete(id);
    }
}

#[spacetimedb::reducer]
pub fn seed_batch(
    ctx: &ReducerContext,
    ids: Vec<u64>,
    scores: Vec<u32>,
    timestamps: Vec<i32>,
) -> Result<(), String> {
    assert_same_len("seed ids/scores", ids.len(), scores.len())?;
    assert_same_len("seed ids/timestamps", ids.len(), timestamps.len())?;

    for ((id, score), timestamp) in ids.into_iter().zip(scores).zip(timestamps) {
        ctx.db.doc().insert(Doc {
            id,
            score,
            name: format!("doc_{id}"),
            timestamp,
        });
    }

    Ok(())
}

#[spacetimedb::reducer]
pub fn apply_tick(
    ctx: &ReducerContext,
    update_ids: Vec<u64>,
    update_scores: Vec<u32>,
    update_timestamps: Vec<i32>,
    insert_ids: Vec<u64>,
    insert_scores: Vec<u32>,
    insert_timestamps: Vec<i32>,
    delete_ids: Vec<u64>,
) -> Result<(), String> {
    assert_same_len("update ids/scores", update_ids.len(), update_scores.len())?;
    assert_same_len(
        "update ids/timestamps",
        update_ids.len(),
        update_timestamps.len(),
    )?;
    assert_same_len("insert ids/scores", insert_ids.len(), insert_scores.len())?;
    assert_same_len(
        "insert ids/timestamps",
        insert_ids.len(),
        insert_timestamps.len(),
    )?;

    for ((id, score), timestamp) in update_ids
        .into_iter()
        .zip(update_scores)
        .zip(update_timestamps)
    {
        if let Some(current) = ctx.db.doc().id().find(id) {
            ctx.db.doc().id().update(Doc {
                score,
                timestamp,
                ..current
            });
        }
    }

    for ((id, score), timestamp) in insert_ids
        .into_iter()
        .zip(insert_scores)
        .zip(insert_timestamps)
    {
        ctx.db.doc().insert(Doc {
            id,
            score,
            name: format!("doc_{id}"),
            timestamp,
        });
    }

    for id in delete_ids {
        if ctx.db.doc().id().find(id).is_some() {
            ctx.db.doc().id().delete(id);
        }
    }

    Ok(())
}

#[spacetimedb::reducer]
pub fn cleanup_all(ctx: &ReducerContext) {
    let docs: Vec<Doc> = ctx.db.doc().iter().collect();
    for current in docs {
        if current.timestamp != -1 {
            ctx.db.doc().id().update(Doc {
                timestamp: -1,
                ..current
            });
        }
    }
}
