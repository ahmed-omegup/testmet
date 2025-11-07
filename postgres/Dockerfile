FROM postgres:18-alpine

# Install build dependencies and build decoderbufs from source
# Alpine doesn't have prebuilt decoderbufs packages, so we build from tagged release
RUN apk add --no-cache --virtual .build-deps \
    build-base \
    postgresql-dev \
    protobuf-c-dev \
    git
RUN apk add --no-cache protobuf-c
RUN cd /tmp && git clone --depth 1 --branch v3.3.0 https://github.com/debezium/postgres-decoderbufs.git
RUN cd /tmp/postgres-decoderbufs && make && make install
RUN cd / && rm -rf /tmp/postgres-decoderbufs && apk del .build-deps

# Copy initialization script
COPY init-decoderbufs.sql /docker-entrypoint-initdb.d/
