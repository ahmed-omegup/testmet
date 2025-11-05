import pkg from 'pg';
const { Client } = pkg;
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
const ELECTRIC_URL = process.env.ELECTRIC_URL;

export async function seedElectric() {
  console.log("=== SEEDING POSTGRESQL (Electric) ===");
  const client = new Client({ connectionString: POSTGRES_URL });
  
  try {
    await client.connect();
    
    // Create table with Electric-compatible schema
    await client.query(`
      DROP TABLE IF EXISTS docs;
    `);
    
    await client.query(`
      CREATE TABLE docs (
        id TEXT PRIMARY KEY,
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

    // In Electric v1.0+, tables must be added to the publication
    await client.query(`
      ALTER PUBLICATION electric_publication_default ADD TABLE docs;
    `);
    console.log("Table added to Electric publication");

    console.log(`Seeding ${N} documents...`);
    
    // Use COPY for bulk insert (fastest method in PostgreSQL)
    const batchSize = 10000;
    for (let i = 0; i < N; i += batchSize) {
      const values = [];
      for (let j = i; j < Math.min(i + batchSize, N); j++) {
        values.push(`('doc_${j}', 'doc_${j}', ${Math.floor(rand() * RANGE)}, ${j})`);
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

export async function spawnCustomersElectric(count, initTime) {
  console.log(`\n=== SPAWNING ${count} CUSTOMERS IN ${initTime}s (Electric) ===`);
  const customers = [];
  const startTime = Date.now();
  
  for (let i = 0; i < count; i++) {
    const ww = i === 0 ? fs.openSync('./log/electric.log', 'w') : null;
    const [minScore, maxScore] = customerRange(i);
    ww && fs.writeSync(ww, '-> ' + new Date() + ': listening to [' + minScore + ' .. ' + maxScore + ']\n', { flag: 'a' });
    
    // Create Electric shape subscription for this customer's range
    const customerPromise = (async () => {
      let n = 0;
      
      try {
        // Subscribe to Electric shape
        // Electric v1.0 Shape API format with WHERE clause for filtering
        const shapeUrl = `${ELECTRIC_URL}/v1/shape?table=docs&offset=-1&where=score >= ${minScore} AND score <= ${maxScore}`;
        
        // Use fetch with streaming
        const response = await fetch(shapeUrl);
        if (!response.ok) {
          throw new Error(`Electric shape request failed: ${response.statusText}`);
        }
        
        const reader = response.body.getReader();
        const decoder = new TextDecoder();
        
        // Process streaming messages
        let buffer = '';
        
        // Wait for cleanup signal
        await new Promise((resolve, reject) => {
          const processChunk = async () => {
            try {
              const { done, value } = await reader.read();
              if (done) {
                ww && fs.closeSync(ww);
                resolve(i);
                return;
              }
              
              buffer += decoder.decode(value, { stream: true });
              const lines = buffer.split('\n');
              buffer = lines.pop() || '';
              
              for (const line of lines) {
                if (!line.trim() || line.trim() === ',') continue;
                
                // Remove leading comma if present
                const cleanLine = line.trim().replace(/^,/, '');
                if (!cleanLine) continue;
                
                try {
                  const message = JSON.parse(cleanLine);
                  ww && fs.writeSync(ww, '<- ' + new Date() + ': ' + cleanLine + '\n', { flag: 'a' });
                  
                  // Electric v1.0 format: {key, value, headers}
                  if (message.value) {
                    const score = parseInt(message.value.score, 10);
                    const timestamp = parseInt(message.value.timestamp, 10);
                    
                    // Filter by score range for this customer
                    if (score >= minScore && score <= maxScore) {
                      const added = timestamp !== -1;
                      const removed = false; // value exists means not removed
                      const delta = (added ? 1 : 0) - (removed ? 1 : 0);
                      
                      if (delta) {
                        n += delta;
                        if (!n) {
                          ww && fs.closeSync(ww);
                          reader.cancel();
                          resolve(i);
                          return;
                        }
                      }
                    }
                  } else if (message.key && !message.value) {
                    // Delete message (null value) - we need to track these during cleanup
                    // Since we can't filter deletes by score, we'll just decrement
                    // This is a limitation of the Electric API
                    n--;
                    if (n <= 0) {
                      ww && fs.closeSync(ww);
                      reader.cancel();
                      resolve(i);
                      return;
                    }
                  }
                } catch (parseErr) {
                  // Ignore parse errors for non-JSON lines
                }
              }
              
              // Continue processing
              processChunk();
            } catch (err) {
              reject(err);
            }
          };
          
          processChunk();
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
  return customers;
}

export async function periodicUpdatesElectric(duration) {
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
        const id = `doc_${Math.floor(rand() * N)}`;
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
        const id = `doc_${N + tick * insertsPerTick + i}`;
        insertValues.push(`('${id}', '${id}', ${Math.floor(rand() * RANGE)}, ${tick})`);
      }
      if (insertValues.length) {
        operations.push(
          client.query(`INSERT INTO docs (id, name, score, timestamp) VALUES ${insertValues.join(', ')}`)
        );
      }
      
      // Deletes
      for (let i = 0; i < deletesPerTick; i++) {
        const id = `doc_${Math.floor(rand() * N)}`;
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
        await sleep(0.01);
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
