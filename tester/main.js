import fs from "fs";
import { MongoClient } from "mongodb";
import WebSocket from "ws";

const MONGO_URL = process.env.MONGO_URL;
const METEOR_URL = process.env.METEOR_URL;
const CUSTOMERS = parseInt(process.env.CUSTOMERS || "20000");
const DURATION = parseInt(process.env.DURATION || "10");
const INIT_TIME = parseInt(process.env.INIT_TIME || "10");
const N = parseInt(process.env.DOCUMENTS || "1000000");

// Deterministic PRNG
function prng(seed) {
  return () => (seed = (seed * 48271) % 0x7fffffff) / 0x7fffffff;
}
const rand = prng(42);

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// Fatal error handler - stop entire cluster on first error
function fatal(msg, err) {
  console.error(`FATAL ERROR: ${msg}`);
  if (err) console.error(err);
  process.exit(1);
}

async function seedDb() {
  console.log("=== SEEDING DATABASE ===");
  const client = new MongoClient(MONGO_URL);
  try {
    await client.connect();
    const db = client.db("benchmark");
    const docs = db.collection("docs");
    
    await docs.drop({});
    console.log("DB cleared");

    console.log(`Seeding ${N} documents...`);
    const bulk = [];
    for (let i = 0; i < N; i++) {
      bulk.push({
        insertOne: {
          document: {
            _id: `doc_${i}`,
            name: `doc_${i}`,
            score: Math.floor(rand() * 1000),
            timestamp: i,
          },
        },
      });
      if (bulk.length === 10_000) {
        await docs.bulkWrite(bulk);
        console.log(`  Inserted ${i + 1}/${N} documents`);
        bulk.length = 0;
      }
    }
    if (bulk.length) await docs.bulkWrite(bulk);
    const [{ total }] = await docs.aggregate([{$count: 'total'}]).toArray();
    console.log(`Seeding complete: ${total}/${N} documents inserted`);
  } catch (err) {
    fatal("Failed to seed database", err);
  } finally {
    await client.close();
  }
}

function customerRange(c) {
  const width = 100 + rand() * 500;
  const a = rand() * (1000 - width);
  return [Math.floor(a), Math.floor(a + width)];
}

async function spawnCustomers(count, initTime) {
  console.log(`\n=== SPAWNING ${count} CUSTOMERS IN ${initTime}s ===`);
  const customers = [];
  const intervalMs = (initTime * 1000) / count; // 100µs for 100k customers in 10s
  const startTime = Date.now();
  
  for (let i = 0; i < count; i++) {
    const ws = new WebSocket('ws://meteor:3000/websocket', {
      handshakeTimeout: 30000
    });
    
    // Fatal error on connection errors
    ws.on('error', (err) => {
      fatal(`WebSocket error for customer ${i}`, err);
    });
    
    // Handle connection and send messages when ready
    const ww = i === 0 ? fs.openSync('./log/ws_message.log', 'w') : null;
    ws.on('open', () => {
      // Send DDP connect message
      const connect = JSON.stringify({ msg: 'connect', version: '1', support: ['1'] })
      ws.send(connect);
      ww && fs.writeSync(ww, '-> ' + new Date() + ': ' + connect + '\n', { flag: 'a' });
      
      // Subscribe to deterministic range
      const [a, b] = customerRange(i);
      const subId = `sub_${i}`;
      const subsMsg = JSON.stringify({ msg: 'sub', id: subId, name: 'latestDocs', params: [a, b] })
      ws.send(subsMsg);
      ww && fs.writeSync(ww, '-> ' + new Date() + ': ' + subsMsg + '\n', { flag: 'a' });
    });

    let n = 0;
    ws.on('message', (data) => {
      try {
        ww && fs.writeSync(ww, '<- ' + new Date() + ': ' + data + '\n', { flag: 'a' });
        const msg = JSON.parse(data);
        if (msg.msg === 'added') n++;
        if (msg.msg === 'removed' || ['changed', 'added'].includes(msg.msg) && msg.fields.timestamp === -1) {
          n--;
          if (n === 0) {
            console.log(`Customer ${i} received all documents, closing connection`);
            ws.close();
          }
        }
      } catch (err) {
        fatal(`Failed to parse message for customer ${i}`, err);
      }
    });

    ws.on('error', (err) => {
      fatal(`WebSocket error for customer ${i}`, err);
    });

    customers.push(new Promise((resolve) => {
      ws.on('close', () => {
        if (n) {
          fatal(`WebSocket closed unexpectedly for customer ${i}, still holding ${n} documents`);
        }
        if(i === 0) fs.closeSync(ww);
        resolve(i);
      });
    }));

    // Progress every 10k customers
    if ((i + 1) % 100 === 0) {
      const elapsed = ((Date.now() - startTime) / 1000).toFixed(2);
      console.log(`Progress: ${i + 1}/${count} customers connected (${elapsed}s)`);
    }
    
    // Wait for next spawn interval
    if (i < count - 1) {
      await sleep(0.01);
    }
  }
  
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`All ${count} customers connected in ${totalTime}s`);
  return customers;
}

async function periodicUpdates(duration) {
  console.log(`\n=== RUNNING UPDATES FOR ${duration}s ===`);
  const client = new MongoClient(MONGO_URL);
  
  try {
    await client.connect();
    const docs = client.db("benchmark").collection("docs");
    
    const updatesPerTick = Math.floor(0.5 * N); // 5% updates
    const insertsPerTick = Math.floor(0.1 * N); // 1% inserts
    const deletesPerTick = Math.floor(0.1 * N); // 1% deletes
    
    for (let tick = 0; tick < duration; tick++) {
      const tickStart = Date.now();
      const bulk = [];
      
      // Updates
      for (let i = 0; i < updatesPerTick; i++) {
        const id = `doc_${Math.floor(rand() * N)}`;
        bulk.push({
          updateOne: {
            filter: { _id: id },
            update: {
              $set: { score: Math.floor(rand() * 1000), timestamp: tick },
            },
          },
        });
      }
      
      // Inserts
      for (let i = 0; i < insertsPerTick; i++) {
        const id = `doc_${N + tick * insertsPerTick + i}`;
        bulk.push({
          insertOne: {
            document: {
              _id: id,
              name: id,
              score: Math.floor(rand() * 1000),
              timestamp: tick,
            },
          },
        });
      }
      
      // Deletes
      for (let i = 0; i < deletesPerTick; i++) {
        const id = `doc_${Math.floor(rand() * N)}`;
        bulk.push({ deleteOne: { filter: { _id: id } } });
      }

      await docs.bulkWrite(bulk).catch(err => fatal(`Bulk write failed at tick ${tick}`, err));
      
      const elapsed = Date.now() - tickStart;
      console.log(`Tick ${tick + 1}/${duration}: ${bulk.length} operations (${elapsed}ms)`);
      
      // Sleep until next tick
      const remaining = 1000 - elapsed;
      if (remaining > 0) {
        await sleep(remaining);
      }
    }
    await docs.updateMany({}, {$set: {timestamp: -1}}); // Clean up after updates
  } catch (err) {
    fatal("Periodic updates failed", err);
  } finally {
    await client.close();
  }
  
  console.log("Periodic updates complete");
}

(async () => {
  try {
    console.log("=== BENCHMARK START ===");
    console.log(`Customers: ${CUSTOMERS}, Init time: ${INIT_TIME}s, Duration: ${DURATION}s\n`);
    
    // Step 1: Seed database
    await seedDb();
   
    // Step 2: Spawn customers with deterministic intervals
    const customers = await spawnCustomers(CUSTOMERS, INIT_TIME);
    
    // Step 3: Run periodic updates
    await periodicUpdates(DURATION);
    
    // Cleanup
    console.log("\n=== WAITING FOR CUSTOMERS TO FINISH ===");
    const res = await Promise.all(customers);
    console.log("\n=== BENCHMARK COMPLETE ===", res);
  } catch (err) {
    fatal("Benchmark failed", err);
  }
})();