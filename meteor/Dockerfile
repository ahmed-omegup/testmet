# Build stage
FROM node:trixie-slim AS builder

WORKDIR /app

# Download and install Meteor
RUN npx --yes meteor

# Initialize Meteor project
RUN meteor create --bare --allow-superuser temp && \
    mv temp/.meteor .meteor && \
    rm -rf temp

# Copy package files
COPY package.json .
RUN npm install

# Copy application code
COPY . .

# Build the Meteor application
RUN meteor build --directory /build --server-only --allow-superuser

# Production stage
FROM node:trixie-slim

WORKDIR /app

# Copy complete built application with all dependencies from builder
COPY --from=builder /build/bundle /app

# Set environment variables
ENV PORT=3000 \
    ROOT_URL=http://localhost:3000

EXPOSE 3000

CMD ["node", "main.js"]