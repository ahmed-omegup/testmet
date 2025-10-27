import { MongoClient } from "mongodb";
import WebSocket from "ws";

const MONGO_URL = process.env.MONGO_URL;
const METEOR_URL = process.env.METEOR_URL;
const CUSTOMERS = parseInt(process.env.CUSTOMERS || "100000");
const DURATION = parseInt(process.env.DURATION || "10");
const INIT_TIME = parseInt(process.env.INIT_TIME || "10");

function prng(seed) {
  return () => (seed = (seed * 48271) % 0x7fffffff) / 0x7fffffff;
}
const rand = prng(42);

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function seedDb() {
  const client = new MongoClient(MONGO_URL);
  await client.connect();
  const db = client.db("benchmark");
  const docs = db.collection("docs");
  await docs.deleteMany({});
  console.log("DB cleared");

  const N = 1_000_000;
  console.log(`Seeding ${N} documents`);
  const bulk = [];
  for (let i = 0; i < N; i++) {
    bulk.push({
      insertOne: {
        document: {
          _id: i,
          name: `doc_${i}`,
          score: Math.floor(rand() * 1000),
          timestamp: i,
        },
      },
    });
    if (bulk.length === 10_000) {
      await docs.bulkWrite(bulk);
      bulk.length = 0;
    }
  }
  if (bulk.length) await docs.bulkWrite(bulk);
  console.log("Seeding done");
  await client.close();
}

function customerRange(c) {
  const a = (c % 1000) * 0.9;
  const width = 50 + (c % 200);
  return [a, Math.min(1000, a + width)];
}

async function spawnCustomers(count) {
  const customers = [];
  let successful = 0;
  let failed = 0;
  
  for (let i = 0; i < count; i++) {
    try {
      const ws = new WebSocket('ws://meteor:3000/websocket', {
        handshakeTimeout: 30000 // 30 second timeout instead of 10
      });
      
      // Add error handler before waiting for open
      ws.on('error', (err) => {
        console.error(`WS error for customer ${i}:`, err.message);
        failed++;
      });
      
      await new Promise((resolve, reject) => {
        const timeout = setTimeout(() => {
          reject(new Error('Connection timeout'));
        }, 30000);
        
        ws.on('open', () => {
          clearTimeout(timeout);
          // Send DDP connect message
          ws.send(JSON.stringify({ msg: 'connect', version: '1', support: ['1'] }));
          resolve();
        });
        
        ws.on('error', (err) => {
          clearTimeout(timeout);
          reject(err);
        });
      });

      // After connection, subscribe to a random range
      const a = Math.floor(prng() * 800000);
      const b = a + 200000;
      const subId = `sub_${i}`;
      ws.send(JSON.stringify({ msg: 'sub', id: subId, name: 'latestDocs', params: [a, b] }));

      customers.push(ws);
      successful++;
      
      // Slow down spawn rate: wait 10ms every 100 connections
      if ((i + 1) % 100 === 0) {
        await new Promise(resolve => setTimeout(resolve, 10));
      }
    } catch (err) {
      failed++;
      console.error(`Failed to spawn customer ${i}:`, err.message);
      // Continue trying to spawn more customers
    }

    if ((successful + failed) % 1000 === 0) {
      console.log(`Progress: ${successful} connected, ${failed} failed (total attempted: ${successful + failed})`);
    }
  }
  
  console.log(`\nFinal: ${successful} customers connected, ${failed} failed`);
  return customers;
}

async function periodicUpdates() {
  const client = new MongoClient(MONGO_URL);
  await client.connect();
  const docs = client.db("benchmark").collection("docs");
  const N = await docs.countDocuments();
  const updates = Math.floor(0.05 * N);
  const inserts = Math.floor(0.01 * N);
  const deletes = Math.floor(0.01 * N);
  let tick = 0;

  while (tick < DURATION) {
    const bulk = [];
    for (let i = 0; i < updates; i++) {
      const id = Math.floor(rand() * N);
      bulk.push({
        updateOne: {
          filter: { _id: id },
          update: {
            $set: { score: Math.floor(rand() * 1000), timestamp: tick },
          },
        },
      });
    }
    for (let i = 0; i < inserts; i++) {
      const id = N + tick * inserts + i;
      bulk.push({
        insertOne: {
          document: {
            _id: id,
            name: `doc_${id}`,
            score: Math.floor(rand() * 1000),
            timestamp: tick,
          },
        },
      });
    }
    for (let i = 0; i < deletes; i++) {
      const id = Math.floor(rand() * N);
      bulk.push({ deleteOne: { filter: { _id: id } } });
    }

    await docs.bulkWrite(bulk);
    console.log(`Tick ${tick}: ${bulk.length} ops`);
    tick++;
    await sleep(1000);
  }

  await client.close();
}

(async () => {
  // Seed database with 1M documents
  await seedDb(1000000);
  
  // Spawn 10,000 simulated customers (realistic load test)
  const customers = await spawnCustomers(10000);
  
  // Run 10 seconds of updates/inserts/deletes
  await periodicUpdates();
  
  // Cleanup
  customers.forEach(ws => ws.close());
  console.log('Benchmark complete!');
  process.exit(0);
})();