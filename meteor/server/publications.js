import { Meteor } from "meteor/meteor";
import { Mongo } from "meteor/mongo";
import { check } from "meteor/check";

export const Docs = new Mongo.Collection("docs");

Meteor.publish("latestDocs", function (a, b) {
  check(a, Number);
  check(b, Number);

  return Docs.find(
    { score: { $gte: a, $lte: b } },
    {
      sort: { timestamp: -1 },
      limit: 50,
      fields: { _id: 1, name: 1, score: 1, timestamp: 1 },
    }
  );
});