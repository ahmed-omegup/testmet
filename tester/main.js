import { RETHINKDB_HOST, POSTGRES_URL, BTREE_URL, CUSTOMERS, INIT_TIME, DURATION, fatal } from "./lib/commons.js";
import { seedMongoDB, spawnCustomersMeteor, periodicUpdatesMongoDB } from "./lib/test-meteor.js";
import { seedRethinkDB, spawnCustomersRethinkDB, periodicUpdatesRethinkDB } from "./lib/test-rethink.js";
import { seedElectric, spawnCustomersElectric, periodicUpdatesElectric } from "./lib/test-electric.js";
import { seedBTree, spawnCustomersBTree, periodicUpdatesBTree } from "./lib/test-btree.js";

// Detect which database we're using
const USE_BTREE = BTREE_URL ? true : false;
const USE_RETHINKDB = RETHINKDB_HOST && !USE_BTREE ? true : false;
const USE_ELECTRIC = POSTGRES_URL && !USE_RETHINKDB && !USE_BTREE ? true : false;

(async () => {
  try {
    console.log("=== BENCHMARK START ===");
    const dbName = USE_BTREE ? 'B-Tree PubSub' : (USE_ELECTRIC ? 'Electric/PostgreSQL' : (USE_RETHINKDB ? 'RethinkDB' : 'MongoDB/Meteor'));
    console.log(`Database: ${dbName}`);
    console.log(`Customers: ${CUSTOMERS}, Init time: ${INIT_TIME}s, Duration: ${DURATION}s\n`);
    
    // Step 1: Seed database
    if (USE_BTREE) {
      await seedBTree();
    } else if (USE_ELECTRIC) {
      await seedElectric();
    } else if (USE_RETHINKDB) {
      await seedRethinkDB();
    } else {
      await seedMongoDB();
    }
   
    // Step 2: Spawn customers with deterministic intervals
    const customers = USE_BTREE
      ? await spawnCustomersBTree(CUSTOMERS, INIT_TIME)
      : (USE_ELECTRIC 
        ? await spawnCustomersElectric(CUSTOMERS, INIT_TIME)
        : (USE_RETHINKDB 
          ? await spawnCustomersRethinkDB(CUSTOMERS, INIT_TIME)
          : await spawnCustomersMeteor(CUSTOMERS, INIT_TIME)));
    
    // Step 3: Run periodic updates
    if (USE_BTREE) {
      await periodicUpdatesBTree(DURATION);
    } else if (USE_ELECTRIC) {
      await periodicUpdatesElectric(DURATION);
    } else if (USE_RETHINKDB) {
      await periodicUpdatesRethinkDB(DURATION);
    } else {
      await periodicUpdatesMongoDB(DURATION);
    }
    
    // Cleanup
    console.log("\n=== WAITING FOR CUSTOMERS TO FINISH ===");
    let n = 0
    customers.forEach(c => c.then(()=>n++));
    const interval = setInterval(() => {
      console.log(`Completed customers: ${n}/${CUSTOMERS}`);
    }, 5000);
    
    // Add timeout to prevent hanging indefinitely
    const timeout = new Promise((_, reject) => 
      setTimeout(() => reject(new Error('Timeout: Customers did not finish within 300s')), 300000)
    );
    
    try {
      const res = await Promise.race([Promise.all(customers), timeout]);
      clearInterval(interval);
      console.log("\n=== BENCHMARK COMPLETE ===");
      console.log(`Successfully completed for ${res.length} customers`);
    } catch (err) {
      clearInterval(interval);
      if (err.message.includes('Timeout')) {
        console.error(`\n!!! ${err.message}`);
        console.error(`Only ${n}/${CUSTOMERS} customers completed`);
        process.exit(1);
      }
      throw err;
    }
  } catch (err) {
    fatal("Benchmark failed", err);
  }
})();
