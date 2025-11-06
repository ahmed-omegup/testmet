#!/bin/bash
set -e

echo "Building Rust binary locally..."
cd btree-pubsub
cargo build --release
docker build -t btree-pubsub .

echo "Done!"
