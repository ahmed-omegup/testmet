FROM node:20

WORKDIR /app

# Meteor 3 CLI (async/await–based)
RUN npm install -g meteor@3.0.0-beta.9

COPY package.json .
RUN npm install

COPY . .

EXPOSE 3000
CMD ["meteor", "run", "--port", "3000", "--once"]