const fs = require('fs');
//const highland = require('highland');
//const Bacon = require('baconjs');

fs.createReadStream('log');


const stupidNumberStream = {
  each: (callback) => {
    setTimeout(() => callback(1), 1000);
    setTimeout(() => callback(2), 2000);
    setTimeout(() => callback(3), 3000);
  }
};

function print(x){
  console.log(x);
}

stupidNumberStream.each(print);
