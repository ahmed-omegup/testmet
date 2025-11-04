import { Meteor } from "meteor/meteor";
import { Mongo } from "meteor/mongo";
import "./publications.js";
import "./seed.js";

Meteor.startup(() => {
  console.log("Meteor benchmark server started");
});