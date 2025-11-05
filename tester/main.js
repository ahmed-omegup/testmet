import { RETHINKDB_HOST, POSTGRES_URL, CUSTOMERS, INIT_TIME, DURATION, fatal } from "./lib/commons.js";
import { seedMongoDB, spawnCustomersMeteor, periodicUpdatesMongoDB } from "./lib/test-meteor.js";
import { seedRethinkDB, spawnCustomersRethinkDB, periodicUpdatesRethinkDB } from "./lib/test-rethink.js";
import { seedElectric, spawnCustomersElectric, periodicUpdatesElectric } from "./lib/test-electric.js";

// Detect which database we're using
const USE_RETHINKDB = RETHINKDB_HOST ? true : false;
const USE_ELECTRIC = POSTGRES_URL ? true : false;

(async () => {
  try {
    console.log("=== BENCHMARK START ===");
    const dbName = USE_ELECTRIC ? 'Electric/PostgreSQL' : (USE_RETHINKDB ? 'RethinkDB' : 'MongoDB/Meteor');
    console.log(`Database: ${dbName}`);
    console.log(`Customers: ${CUSTOMERS}, Init time: ${INIT_TIME}s, Duration: ${DURATION}s\n`);
    
    // Step 1: Seed database
    if (USE_ELECTRIC) {
      await seedElectric();
    } else if (USE_RETHINKDB) {
      await seedRethinkDB();
    } else {
      await seedMongoDB();
    }
   
    // Step 2: Spawn customers with deterministic intervals
    const customers = USE_ELECTRIC 
      ? await spawnCustomersElectric(CUSTOMERS, INIT_TIME)
      : (USE_RETHINKDB 
        ? await spawnCustomersRethinkDB(CUSTOMERS, INIT_TIME)
        : await spawnCustomersMeteor(CUSTOMERS, INIT_TIME));
    
    // Step 3: Run periodic updates
    if (USE_ELECTRIC) {
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
    const res = await Promise.all(customers);
    clearInterval(interval);
    console.log("\n=== BENCHMARK COMPLETE ===");
    console.log(`Successfully completed for ${res.length} customers`);
  } catch (err) {
    fatal("Benchmark failed", err);
  }
})();
