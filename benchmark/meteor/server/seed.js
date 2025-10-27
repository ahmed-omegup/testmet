import { Meteor } from "meteor/meteor";
import { Docs } from "./publications.js";

Meteor.startup(async () => {
  const count = await Docs.find().countAsync();
  if (count === 0) {
    const N = 1_000_000;
    console.log(`Seeding ${N} documents`);
    for (let i = 0; i < N; i++) {
      await Docs.insertAsync({
        _id: i,
        name: `doc_${i}`,
        score: Math.random() * 1000,
        timestamp: i,
      });
    }
    console.log("Seeding done");
  }
});