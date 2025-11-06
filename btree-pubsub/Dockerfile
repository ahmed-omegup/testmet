FROM debian:sid-slim

RUN apt-get update && apt-get install -y \
    libssl3 \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Copy pre-built binary from local machine
COPY target/release/btree-pubsub /app/btree-pubsub

ENV RUST_LOG=info
ENV POSTGRES_URL=postgresql://postgres:postgres@postgres:5432/benchmark

EXPOSE 8080

CMD ["/app/btree-pubsub"]
