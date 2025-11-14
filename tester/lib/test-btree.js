import pkg from 'pg';
const { Client } = pkg;
import WebSocket from 'ws';
import fs from 'fs';
import {
  CUSTOMERS,
  N,
  RANGE,
  rand,
  sleep,
  fatal,
  customerRange
} from "./commons.js";

const POSTGRES_URL = process.env.POSTGRES_URL;
const BTREE_URL = process.env.BTREE_URL;

export async function seedBTree() {
  console.log("=== SEEDING POSTGRESQL (B-Tree PubSub) ===");
  const client = new Client({ connectionString: POSTGRES_URL });
  
  try {
    await client.connect();
    
    // Create table
    await client.query(`
      DROP TABLE IF EXISTS docs;
    `);
    
    await client.query(`
      CREATE TABLE docs (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        score INTEGER NOT NULL,
        timestamp INTEGER NOT NULL
      );
    `);
    
    // Create index on score for efficient queries
    await client.query(`
      CREATE INDEX idx_docs_score ON docs(score);
    `);
    
    console.log("Table created");

    // Add table to publication for logical replication
    await client.query(`
      DROP PUBLICATION IF EXISTS electric_publication_default;
    `);
    
    await client.query(`
      CREATE PUBLICATION electric_publication_default FOR TABLE docs;
    `);
    console.log("Publication created");

    // Set REPLICA IDENTITY FULL to ensure all columns (including timestamp) are sent in replication
    await client.query(`
      ALTER TABLE docs REPLICA IDENTITY FULL;
    `);
    console.log("REPLICA IDENTITY FULL set");

    console.log(`Seeding ${N} documents...`);
    
    const batchSize = 10000;
    for (let i = 0; i < N; i += batchSize) {
      const values = [];
      for (let j = i; j < Math.min(i + batchSize, N); j++) {
        values.push(`(${j}, 'doc_${j}', ${Math.floor(rand() * RANGE)}, ${j})`);
      }
      
      await client.query(`
        INSERT INTO docs (id, name, score, timestamp)
        VALUES ${values.join(', ')}
      `);
      
      console.log(`  Inserted ${Math.min(i + batchSize, N)}/${N} documents`);
    }
    
    const result = await client.query('SELECT COUNT(*) as count FROM docs');
    console.log(`Seeding complete: ${result.rows[0].count}/${N} documents inserted`);
  } catch (err) {
    fatal("Failed to seed PostgreSQL", err);
  } finally {
    await client.end();
  }
}

export async function spawnCustomersBTree(count, initTime) {
  console.log(`\n=== SPAWNING ${count} CUSTOMERS IN ${initTime}s (B-Tree PubSub) ===`);
  const customers = [];
  const startTime = Date.now();
  
  for (let i = 0; i < count; i++) {
    const ww = i === 0 ? fs.openSync('./log/btree.log', 'w') : null;
    const [minScore, maxScore] = customerRange(i);
    ww && fs.writeSync(ww, '-> ' + new Date() + ': listening to [' + minScore + ' .. ' + maxScore + ']\n', { flag: 'a' });
    
    // Create WebSocket connection
    const customerPromise = (async () => {
      let n = 0;
      let logClosed = false;
      let done = false;
      
      return new Promise((resolve, reject) => {
        const ws = new WebSocket(BTREE_URL);
        let connectionId = null;
        
        const closeLog = () => {
          if (ww && !logClosed) {
            fs.closeSync(ww);
            logClosed = true;
          }
        };

        const finish = () => {
          if (done) return;
          done = true;
          try { closeLog(); } catch {}
          try {
            if (ws && (ws.readyState === WebSocket.OPEN || ws.readyState === WebSocket.CONNECTING)) {
              console.log('bye')
              ws.terminate(); // force-close to avoid lingering sockets
            } else {
            console.log('error2')

            }
          } catch {
            console.log('error')
          }
          resolve(i);
        };
        
        ws.on('open', () => {
          // Wait for connection ID first
        });
        
        ws.on('message', (data) => {
          try {
            const msg = JSON.parse(data.toString());
            ww && fs.writeSync(ww, '<- ' + new Date() + ': ' + data.toString() + '\n', { flag: 'a' });
            
            if (msg.type === 'connected') {
              connectionId = msg.connection_id;
              // Subscribe to range
              const subscribeMsg = JSON.stringify({
                type: 'subscribe',
                min_score: minScore,
                max_score: maxScore
              });
              ws.send(subscribeMsg);
              ww && fs.writeSync(ww, '-> ' + new Date() + ': ' + subscribeMsg + '\n', { flag: 'a' });
            } else if (msg.type === 'subscribed') {
              // Subscription confirmed
            } else if (msg.type === 'added') {
              if (msg.timestamp !== -1) {
                n++;
              }
            } else if (msg.type === 'updated') {
              // Score might have changed, check if still in range
              if (msg.timestamp === -1) {
                // Cleanup started
                n--;
                if (n <= 0) {
                  finish();
                }
              }
            } else if (msg.type === 'removed') {
              n--;
              if (n <= 0) {
                finish();
              }
            }
          } catch (err) {
            fatal(`Failed to parse message for customer ${i}`, err);
          }
        });
        
        ws.on('error', (err) => {
          if (!done) {
            fatal(`WebSocket error for customer ${i}`, err);
          }
        });
        
        ws.on('close', () => {
          if (!done && n > 0) {
            fatal(`WebSocket closed unexpectedly for customer ${i}, still holding ${n} documents`);
          }
          finish();
        });
      });
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
  return customers;
}

export async function periodicUpdatesBTree(duration) {
  console.log(`\n=== RUNNING UPDATES FOR ${duration}s ===`);
  const client = new Client({ connectionString: POSTGRES_URL });
  
  try {
    await client.connect();
    
    const updatesPerTick = Math.floor(0.05 * N); // 5% updates
    const insertsPerTick = Math.floor(0.01 * N); // 1% inserts
    const deletesPerTick = Math.floor(0.01 * N); // 1% deletes

    console.log('******', updatesPerTick + insertsPerTick + deletesPerTick);
    
    const allStart = Date.now();
    for (let tick = 0; tick < duration; tick++) {
      const tickStart = Date.now();
      const operations = [];
      
      // Updates
      for (let i = 0; i < updatesPerTick; i++) {
        const id = Math.floor(rand() * N);
        operations.push(
          client.query(
            'UPDATE docs SET score = $1, timestamp = $2 WHERE id = $3',
            [Math.floor(rand() * RANGE), tick, id]
          )
        );
      }
      
      // Inserts
      const insertValues = [];
      for (let i = 0; i < insertsPerTick; i++) {
        const id = N + tick * insertsPerTick + i;
        insertValues.push(`(${id}, 'doc_${id}', ${Math.floor(rand() * RANGE)}, ${tick})`);
      }
      if (insertValues.length) {
        operations.push(
          client.query(`INSERT INTO docs (id, name, score, timestamp) VALUES ${insertValues.join(', ')}`)
        );
      }
      
      // Deletes
      for (let i = 0; i < deletesPerTick; i++) {
        const id = Math.floor(rand() * N);
        operations.push(
          client.query('DELETE FROM docs WHERE id = $1', [id])
        );
      }

      await Promise.all(operations).catch(err => fatal(`Operations failed at tick ${tick}`, err));
      
      const elapsed = Date.now() - tickStart;
      const overAllElapsed = Date.now() - allStart;
      console.log(`Tick ${tick + 1}/${duration}: ${operations.length} operations (${Math.round(overAllElapsed/100)/10}s)`);
      
      // Sleep until next tick
      const remaining = 1000 - elapsed;
      if (remaining > 0) {
        await sleep(remaining);
      }
    }
    
    // Cleanup - mark all documents for removal
    await client.query('UPDATE docs SET timestamp = -1');
    
  } catch (err) {
    fatal("Periodic updates failed", err);
  } finally {
    await client.end();
  }
  
  console.log("Periodic updates complete");
}
