FROM postgres:18-alpine

# Install build dependencies and build decoderbufs from source
# Alpine doesn't have prebuilt decoderbufs packages, so we build from tagged release
RUN apk add --no-cache --virtual .build-deps
RUN apk add --no-cache build-base
RUN apk add --no-cache postgresql-dev
RUN apk add --no-cache protobuf-c-dev
RUN apk add --no-cache git
RUN apk add --no-cache protobuf-c
RUN cd /tmp && git clone --depth 1 https://github.com/debezium/postgres-decoderbufs.git
RUN apk add --no-cache clang19
RUN apk add --no-cache proj-dev
RUN apk add --no-cache geos-dev
RUN apk add --no-cache pkgconfig
RUN cd /tmp/postgres-decoderbufs && make && cp decoderbufs.so $(pg_config --pkglibdir)/ && cp decoderbufs.control $(pg_config --sharedir)/extension/
RUN cd / && rm -rf /tmp/postgres-decoderbufs && apk del .build-deps

# Copy initialization script
COPY init-decoderbufs.sql /docker-entrypoint-initdb.d/
