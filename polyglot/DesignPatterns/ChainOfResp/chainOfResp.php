<?php
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
// design pattern can be successfully applied, allowing the implementation 
// of the ATM machine to forget about all those different services and 
// the details of how to convert an amount of cash into a set of notes.
//
//
// Our ATM machine only need to worry about the head of the chain of
// services, which it maintains as an internal data member. This machine
// has the ability to provide a set of bank notes from a desired amount
class ATMMachine {
  // private data member representing the head of the chain of handlers
  private $handler;
  public function __construct(){ 
    $this->handler = RequestHandler::getHandlingChain(); 
  }
  // main functionality
  public function getAmount($amount){
    echo "ATM machine: requesting amount of \${$amount}\n";
    return $this->handler->handleRequest($amount);  // delegates request to chain
  }
}

// This is the base class, uniting all request handlers into a common
// interface. This class in normally abstract (the whole point of the
// design pattern is dealing with multiple types of request).
abstract class RequestHandler {
  private $next;
  public function __construct($next){ $this->next = $next; }
  
  // setting up the chain of responsibility. In our case, the request
  // handler responsible of the delivery of $50 notes will intervene
  // first, then pass on request to its successor
  public static function getHandlingChain(){
    $handler = new RequestHandlerForFive(null);
    $handler = new RequestHandlerForTen($handler);
    $handler = new RequestHandlerForTwenty($handler);
    $handler = new RequestHandlerForFifty($handler);
    return $handler;
  }
 
  // This is the main method of the class. It is often an abstract
  // method as the diffeent types of request handlers may have little
  // in common. In our case, all request handlers are similar and only
  // differ in the specific denomination of the bank note they deliver.
  // Such denominations are encoded in a virtual method.
  public function handleRequest($amount){
    if($amount < 0) throw new InvalidArgumentException();
    if($amount == 0) return [];
    if($amount % 5 != 0){ // modulo
      throw new InvalidArgumentException("Amount should be multiple of 5");
    }
    // handleRequest logic is the same across all request handlers
    // in our case. However, this logic is parameterized by denomination
    // This is a case of mini-template method design pattern.
    $denom = $this->denomination();
    $value = $denom->value();
    $addSingleNote = false;   // whether handler should give way note

    if($amount >= $value){
      $list = $this->handleRequest($amount - $value);   // recursive call
      $addSingleNote = true;
    } else {
      if($this->next != null){
        $list = $this->next->handleRequest($amount);    // passing on request
      } else {
        throw new Exception("Illegal State");           // chain badly set up
      }
    }

    // set of bank notes obtained by a mixture of recursive call and 
    // delegation of request to the next handler on the chain. We 
    // should not forget to add a single note if required.
    if($addSingleNote) $list[] = $denom; // appending to list, add, push 

    return $list;
  }

  public abstract function denomination();
} 

// delivers $50 notes
class RequestHandlerForFifty extends RequestHandler {
  public function __construct($next){ parent::__construct($next); }
  public function denomination(){ return new Fifty; }
}

// delivers $20 notes
class RequestHandlerForTwenty extends RequestHandler {
  public function __construct($next){ parent::__construct($next); }
  public function denomination(){ return new Twenty; }
}

// delivers $10 notes
class RequestHandlerForTen extends RequestHandler {
  public function __construct($next){ parent::__construct($next); }
  public function denomination(){ return new Ten; }
}

// delivers $5 notes
class RequestHandlerForFive extends RequestHandler {
  public function __construct($next){ parent::__construct($next); }
  public function denomination(){ return new Five; }
}

abstract class BankNote {
  public abstract function value();
  public function __toString(){ return "{$this->value()}"; }
  public static function printList($list){
    $startFlag = true;
    echo "[";
    foreach($list as $item){
      if($startFlag){
        $startFlag = false;
      } else {
        echo ", ";
      }
      echo $item;
    }
    echo "]";
  }
}

class Five extends BankNote {
  public function value(){ return 5; }
}

class Ten extends BankNote {
  public function value(){ return 10; }
}

class Twenty extends BankNote {
  public function value(){ return 20; }
}

class Fifty extends BankNote {
  public function value(){ return 50; }
}

// main
$atm = new ATMMachine;
$list = $atm->getAmount(235);
echo "The notes handed out by the ATM machine are:\n";
BankNote::printList($list);
echo "\n";





?>
