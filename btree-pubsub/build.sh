#!/bin/bash
set -e

echo "Building Rust binary locally..."
cargo build --release

echo "Building Docker image..."
docker build -t btree-pubsub .

echo "Done!"
