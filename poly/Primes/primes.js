// A very reasonable performance from JavaScript on this one

// TODO: make this work with nodejs

// We did not implement memoization in the thunk. We initially forgot,
// then realized it had no beneficial impact in the Scheme implementation
//
// there is no assert function in javascript
function assert(condition) {
  if (!condition) {
    throw "Assertion failed";
  }
}

function Cell(head, tail){
  this.car = head;
  this.cdr = function(){ return tail; }   // thunk
}

Cell.prototype.first  = function(){ return this.car; }
Cell.prototype.rest   = function(){ return this.cdr(); }
Cell.prototype.take   = function(N){
  assert(N > 0);
  var cell = new Cell(this.first(), null);
  if(N == 1) return cell;
  // defining var func = this.rest will fail for some reason
  var func = this.cdr;  // cannot put 'this' into lambda expression
  cell.cdr = function(){ return func().take(N-1); };
  return cell;
}
Cell.prototype.toString = function(){
  var str = "(";
  var start = true;
  var next = this;
  while(next != null){
    if(!start){
      str += " ";
    }
    else{
      start = false;
    }
    str += next.first();
    next = next.rest();
  }
  return str + ")";
}
Cell.prototype.filter = function(predicate){
  var next = this;
  while(!predicate(next.first())){
    next = next.rest();
  }
  var cell = new Cell(next.first(), null);
  cell.cdr = function(){ return next.rest().filter(predicate); };
  return cell;
}  

Cell.fromTransition = function(init, transition){
  var cell = new Cell(init, null);
  cell.cdr = function(){ 
    return Cell.fromTransition(transition(init), transition); 
  };
  return cell;
}

Cell.sieve = function(input, paramPredicate){
  var x = input.first();
  var cell = new Cell(x, null);
  cell.cdr = function(){
    return Cell.sieve(input.rest().filter(function(n){ 
      return paramPredicate(n,x);
    }), paramPredicate);
  };
  return cell;
}

// 'scriptArgs' works for this interpreter (spidermonkey)
// command line arguments

var numPrimes = Number(process.argv[2]);

from2 = Cell.fromTransition(2, function(n){ return n+1; });
primes = Cell.sieve(from2, function(n,x){ return n % x != 0; });
console.log(primes.take(numPrimes))

