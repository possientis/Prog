// Chain of Responsibility Design Pattern

// The Chain Of Responsibility design pattern is meant to decouple
// clients (which may have various requests) from request handlers
// which may be of different types. Rather than forcing a client
// to have the precise knowledge of which request handler is able
// to deal with which type of request, the Chain of Responsibility
// design pattern creates a common base interface to all request
// handlers, and unites them into a single linked list (a 'chain').
// Now the client only needs to know the head of the chain, to
// which it sends all of its requests. Each request handler, apart
// from maintaining a link to a 'successor', fundamentally has
// a 'handleRequest' method which now accepts all types of request.
// However, when faced with a request which it cannot fulfill, a 
// request handler will pass on the request to its successor. 
// Provided the chain of request handlers is properly set up, all
// requests should be handled appropriately.
//
// Note that this pattern can be generalized from 'chains' to non
// linear structure between objects, such as trees. One can imagine
// a network of request handlers, which are either dealing with 
// request themselves, or passing requests to other (linked) 
// request handlers
//
// This coding exercise is meant to provide a simulation of an ATM
// machine. As a server, the machine is able to provide a service
// 'getAmount' to an external client which consists in the delivery
// of the appropriate set of bank notes which corresponds to a 
// desired amount. As a client, the ATM machine relies on various
// request handlers, namely those which are specialized in the delivery
// of specific bank notes. So the machine relies on a service for the 
// delivery of $5 notes, another service for the delivery of $10 notes
// and so forth. This is a case where the Chain of Responsibility 
// design pattern can be succesfully applied, allowing the implementation 
// of the ATM machine to forget about all those different services and 
// the details of how to convert an amount of cash into a set of notes.


// Our ATM machine only need to worry about the head of the chain of
// services, which it maintains as an internal data member. This machine
// has the ability to provide a set of bank notes from a desired amount

function ATMMachine(){
  // data member representing the head of the chain of handlers
  this._handler = RequestHandler.getHandlingChain();
}
ATMMachine.prototype.getAmount = function(amount){
  print("ATM machine: requesting amount of $" + amount);
  return this._handler.handleRequest(amount); // delegates request to chain
}


// This is the base class, uniting all request handlers into a common
// interface. This class in normally abstract (the whole point of the
// design pattern is dealing with multiple types of request).
function RequestHandler(next) {
  this._next = next;  // successor
}

// setting up the chain of responsibility. In our case, the request
// handler responsible of the delivery of $50 notes will intervene
// first, then pass on request to its successor
RequestHandler.getHandlingChain = function(){
  var handler = new RequestHandlerForFive(null);
      handler = new RequestHandlerForTen(handler);
      handler = new RequestHandlerForTwenty(handler);
      handler = new RequestHandlerForFifty(handler);
  return handler;
}

// This is the main method of the class. It is often an abstract
// method as the diffeent types of request handlers may have little
// in common. In our case, all request handlers are similar and only
// differ in the specific denomination of the bank note they deliver.
// Such denominations are encoded in a virtual method.
RequestHandler.prototype.handleRequest = function(amount){
  if(amount < 0)      { throw "Requested amount should be non-negative"; }
  if(amount == 0)     { return new Array(); }  // empty list
  if(amount % 5 != 0) { throw "Requested amount should be multiple of $5"; }

  // handleRequest logic is the same across all request handlers
  // in our case. However, this logic is parameterized by denomination
  // This is a case of mini-template method design pattern.
  var denom = this.denomination();
  var value = denom.value;
  var addSingleNote = false;  // whether handler gives away note
  var list = undefined;       // will be returned after request completion

  if(amount >= value){
    list = this.handleRequest(amount - value);  // recursive call
    addSingleNote = true;                       // handler should give note
  } else {
    if(this._next != null){
      list = this._next.handleRequest(amount);  // passing on request
    } else {
      throw "Illegal state: chain badly set up"
    }
  }
  // set of bank notes obtained by a mixture of recursive call and 
  // delegation of request to the next handler on the chain. We 
  // should not forget to add a single note if required.
  if(addSingleNote){ list.push(denom); }  // adding to array

  return list;
}

// This is what distinguishes one handdler from another
// Hence the method is abstract
RequestHandler.prototype.denomination = function(){
  throw "RequestHandler::denomination is not implemented";
}

// delivers $50 notes
function RequestHandlerForFifty(next){ RequestHandler.call(this, next); }
RequestHandlerForFifty.prototype = Object.create(RequestHandler.prototype);
RequestHandlerForFifty.prototype.denomination = function(){ return Fifty; }

// delivers $20 notes
function RequestHandlerForTwenty(next){ RequestHandler.call(this, next); }
RequestHandlerForTwenty.prototype = Object.create(RequestHandler.prototype);
RequestHandlerForTwenty.prototype.denomination = function(){ return Twenty; }

// delivers $10 notes
function RequestHandlerForTen(next){ RequestHandler.call(this, next); }
RequestHandlerForTen.prototype = Object.create(RequestHandler.prototype);
RequestHandlerForTen.prototype.denomination = function(){ return Ten; }

// delivers $5 notes
function RequestHandlerForFive(next){ RequestHandler.call(this, next); }
RequestHandlerForFive.prototype = Object.create(RequestHandler.prototype);
RequestHandlerForFive.prototype.denomination = function(){ return Five; }

var Five    = { value: 5 };
var Ten     = { value: 10};
var Twenty  = { value: 20};
var Fifty   = { value: 50};


var listToString = function(list){
  var str = "[";
  var i = 0;
  var start = true;
  for(i = 0; i < list.length; ++i){
    if(start){
      start = false;
    } else {
      str = str + ", ";
    }
    str = str + list[i].value;
  }
  str = str + "]";
  return str;
}

// main
var atm = new ATMMachine();
var list = atm.getAmount(235);
print("The notes handed out by the ATM machine are:");
print(listToString(list));





 

