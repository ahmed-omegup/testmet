FROM node:20

WORKDIR /app

# Install dependencies
RUN npm install rethinkdb ws express

COPY server.js .

EXPOSE 3000

CMD ["node", "server.js"]
