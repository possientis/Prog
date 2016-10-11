const fetch = require('node-fetch')
//const co = require('co')

/*
fetch('http://jsonplaceholder.typicode.com/posts/1')
  .then( response => response.json() )
  .then( post => post.title )
  .then( x => console.log('Title:', x) )
*/

/*
co(function *() {
  const uri = 'http://jsonplaceholder.typicode.com/posts/1';
  const response = yield fetch(uri);
  const post  = yield response.json();
  const title = post.title;
  console.log('Title:', title);
})
*/

run(function *() {
  const uri = 'http://jsonplaceholder.typicode.com/posts/1';
  const response = yield fetch(uri);
  console.log('response is', response);
  const post  = yield response.json();
  const title = post.title;
  console.log('Title:', title);
})


function run(generator){
  const iterator = generator();
  const iteration = iterator.next();
  const promise = iteration.value;
  promise.then(x => iterator.next(x));
}
