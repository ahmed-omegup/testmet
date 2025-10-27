FROM node:20

WORKDIR /app

# Install Meteor
RUN curl https://install.meteor.com/ | sh

# Initialize Meteor project
RUN meteor create --release 3.0.2 --bare --allow-superuser temp && \
    mv temp/.meteor .meteor && \
    rm -rf temp

COPY package.json .
RUN npm install

COPY . .

EXPOSE 3000
CMD ["meteor", "run", "--port", "3000", "--release", "3.0.2"]