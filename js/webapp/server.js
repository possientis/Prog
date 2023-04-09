const { readFileSync, writeFileSync } = require('fs')

const express = require('express')

const app = express();

app.get('/', (req, res) => {
  const count = readFileSync('./count.txt');
  console.log('count ', count);
  const newCount = parseInt(count) + 1;
  writeFileSync('./count.txt', newCount.toString());

  res.send(`

    <!DOCTYPE html>
    <html lang="en">
    <head>
      <meta charset="utf-8" />
      <meta name="viewport" content="width=device-width, initial-scale=1" />
      <title>RPi Hosted Website</title>
    </head>
    <body>
      <hi>Welcome to my Website!</hi>
      <p>This page has been viewed ${newCount} times!</p>
    </body>
    </html>
  `);
});


app.listen(5000, () => console.log('http://localhost:5000/'));
