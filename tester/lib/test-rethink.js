import fs from "fs";
import r from "rethinkdb";
import {
  RETHINKDB_HOST,
  RETHINKDB_PORT,
  N,
  RANGE,
  rand,
  sleep,
  fatal,
  customerRange
} from "./commons.js";

export async function seedRethinkDB() {
  console.log("=== SEEDING RETHINKDB ===");
  let conn = null;
  try {
    conn = await r.connect({ host: RETHINKDB_HOST, port: RETHINKDB_PORT });
    
    // Clear existing data
    try {
      await r.db('benchmark').table('docs').delete().run(conn);
      console.log("DB cleared");
    } catch (err) {
      // Table might not exist yet
      console.log("Table not found, will be created");
    }

    // Ensure database and table exist
    try {
      const dbList = await r.dbList().run(conn);
      if (!dbList.includes('benchmark')) {
        await r.dbCreate('benchmark').run(conn);
        console.log('Created database: benchmark');
      }
      
      const tableList = await r.db('benchmark').tableList().run(conn);
      if (!tableList.includes('docs')) {
        await r.db('benchmark').tableCreate('docs').run(conn);
        console.log('Created table: docs');
        
        // Create index on score for efficient queries
        await r.db('benchmark').table('docs').indexCreate('score').run(conn);
        await r.db('benchmark').table('docs').indexWait('score').run(conn);
        console.log('Created index on score');
      }
    } catch (err) {
      console.error('Setup database error:', err);
    }

    console.log(`Seeding ${N} documents...`);
    const batchSize = 10000;
    for (let i = 0; i < N; i += batchSize) {
      const batch = [];
      for (let j = i; j < Math.min(i + batchSize, N); j++) {
        batch.push({
          id: `doc_${j}`,
          name: `doc_${j}`,
          score: Math.floor(rand() * RANGE),
          timestamp: j,
        });
      }
      await r.db('benchmark').table('docs').insert(batch).run(conn);
      console.log(`  Inserted ${Math.min(i + batchSize, N)}/${N} documents`);
    }
    
    const count = await r.db('benchmark').table('docs').count().run(conn);
    console.log(`Seeding complete: ${count}/${N} documents inserted`);
  } catch (err) {
    fatal("Failed to seed RethinkDB", err);
  } finally {
    if (conn) await conn.close();
  }
}

export async function spawnCustomersRethinkDB(count, initTime) {
  console.log(`\n=== SPAWNING ${count} CUSTOMERS IN ${initTime}s (RethinkDB) ===`);
  const customers = [];
  const intervalMs = (initTime * 1000) / count;
  const startTime = Date.now();
  
  // Create connection pool for customers
  const conn = await r.connect({ host: RETHINKDB_HOST, port: RETHINKDB_PORT });
  
  for (let i = 0; i < count; i++) {
    const ww = i === 0 ? fs.openSync('./log/rethinkdb.log', 'w') : null;
    const [minScore, maxScore] = customerRange(i);
    ww && fs.writeSync(ww, '-> ' + new Date() + ': listening to [' + minScore + ' .. ' + maxScore + ']\n', { flag: 'a' });
    
    // Create changefeed for this customer's range
    const customerPromise = (async () => {
      let n = 0;
      
      try {
        
        // Setup changefeed
        const cursor = await r.db('benchmark')
          .table('docs')
          .between(minScore, maxScore, { index: 'score' })
          .changes({ includeInitial: true })
          .run(conn);
        
        // Wait for cleanup signal
        await new Promise((resolve, reject) => {
          cursor.each((err, change) => {
            if (err) {
              reject(err);
              return;
            }
            ww && fs.writeSync(ww, '<- ' + new Date() + ': ' + JSON.stringify(change) + '\n', { flag: 'a' });

            const added = change.new_val && change.new_val.timestamp !== -1;
            const removed = change.old_val && change.old_val.timestamp !== -1;
            const delta = (added ? 1 : 0) - (removed ? 1 : 0);            
            if (delta) {
              // Document removed during cleanup
              n += delta;
              if (!n) {
                ww && fs.closeSync(ww);
                cursor.close();
                resolve(i);
              }
            }
          });
        });
        
        return i;
      } catch (err) {
        fatal(`Customer ${i} failed`, err);
      }
    })();
    
    customers.push(customerPromise);
    
    // Progress logging
    if ((i + 1) % 100 === 0) {
      const elapsed = ((Date.now() - startTime) / 1000).toFixed(2);
      console.log(`Progress: ${i + 1}/${count} customers spawned (${elapsed}s)`);
    }
    
    // Wait for next spawn interval
    if (i < count - 1) {
      await sleep(0.01);
    }
  }
  
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`All ${count} customers spawned in ${totalTime}s`);
  Promise.all(customers).then(()=>conn.close())
  return customers;
}

export async function periodicUpdatesRethinkDB(duration) {
  console.log(`\n=== RUNNING UPDATES FOR ${duration}s ===`);
  let conn = null;
  
  try {
    conn = await r.connect({ host: RETHINKDB_HOST, port: RETHINKDB_PORT });
    const table = r.db('benchmark').table('docs');
    
    const updatesPerTick = Math.floor(0.05 * N); // 5% updates
    const insertsPerTick = Math.floor(0.01 * N); // 1% inserts
    const deletesPerTick = Math.floor(0.01 * N); // 1% deletes

    console.log('******', updatesPerTick + insertsPerTick + deletesPerTick)
    
    for (let tick = 0; tick < duration; tick++) {
      const tickStart = Date.now();
      const operations = [];
      
      // Updates
      for (let i = 0; i < updatesPerTick; i++) {
        const id = `doc_${Math.floor(rand() * N)}`;
        operations.push(
          table.get(id).update({
            score: Math.floor(rand() * RANGE),
            timestamp: tick
          }).run(conn)
        );
      }
      
      // Inserts
      const inserts = [];
      for (let i = 0; i < insertsPerTick; i++) {
        const id = `doc_${N + tick * insertsPerTick + i}`;
        inserts.push({
          id: id,
          name: id,
          score: Math.floor(rand() * RANGE),
          timestamp: tick,
        });
      }
      if (inserts.length) {
        operations.push(table.insert(inserts).run(conn));
      }
      
      // Deletes
      for (let i = 0; i < deletesPerTick; i++) {
        const id = `doc_${Math.floor(rand() * N)}`;
        operations.push(table.get(id).delete().run(conn));
      }

      await Promise.all(operations).catch(err => fatal(`Operations failed at tick ${tick}`, err));
      
      const elapsed = Date.now() - tickStart;
      console.log(`Tick ${tick + 1}/${duration}: ${operations.length} operations (${elapsed}ms)`);
      
      // Sleep until next tick
      const remaining = 1000 - elapsed;
      if (remaining > 0) {
        await sleep(remaining);
      }
    }
    await table.update({timestamp: -1}).run(conn); // Clean up after updates
  } catch (err) {
    fatal("Periodic updates failed", err);
  } finally {
    if (conn) await conn.close();
  }
  
  console.log("Periodic updates complete");
}
