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


// Our ATM machine only need to worry about the head of the chain of
// services, which it maintains as an internal data member. This machine
// has the ability to provide a set of bank notes from a desired amount
class ATMMachine {
  // private data member representing the head of the chain of handlers
  private val _handler = RequestHandler.getHandlingChain
  // main functionality
  def getAmount(amount: Int): List[BankNote] = {
    println("ATM machine: requesting amount of $" + amount)
    _handler.handleRequest(amount)  // delegates request to chain
  }
}

// This is the base class, uniting all request handlers into a common
// interface. This class in normally abstract (the whole point of the
// design pattern is dealing with multiple types of request).
abstract class RequestHandler(next : RequestHandler){
  // This is the main method of the class. It is often an abstract
  // method as the diffeent types of request handlers may have little
  // in common. In our case, all request handlers are similar and only
  // differ in the specific denomination of the bank note they deliver.
  // Such denominations are encoded in a virtual method.
  def handleRequest(amount: Int): List[BankNote] = {
    if(amount < 0) throw new IllegalArgumentException
    if(amount == 0) return Nil  // empty list
    if(amount % 5 != 0) throw new IllegalArgumentException(
      "Requested amount should be multiple of $5");

    // handleRequest logic is the same across all request handlers
    // in our case. However, this logic is parameterized by denomination
    // This is a case of mini-template method design pattern.
    val denom = this.denomination
    val value = denom.value
    var addSingleNote : Boolean = false   // whether handler gives away note
    var list : List[BankNote] = Nil // will be returned after request complete 

    if(amount >= value){
      list = handleRequest(amount - value)  // recursive call
      addSingleNote = true                  // handler should give note
    } else {
      if(next != null){
        list = next.handleRequest(amount)   // passing on request
      } else {
        throw new IllegalStateException()   // chain badly set up
      }
    }
    // set of bank notes obtained by a mixture of recursive call and 
    // delegation of request to the next handler on the chain. We 
    // should not forget to add a single note if required.
    if(addSingleNote) list = denom :: list;     // cons

    list  // returning list
  }

  // This is what distinguishes one handdler from another
  // Hence the method is abstract
  def denomination : BankNote; 
}

object RequestHandler { // static class member in companion object
  def getHandlingChain : RequestHandler = {
    var handler : RequestHandler  = new RequestHandlerForFive(null)
        handler                   = new RequestHandlerForTen(handler)
        handler                   = new RequestHandlerForTwenty(handler)
        handler                   = new RequestHandlerForFifty(handler)
        handler
  }
}

class RequestHandlerForFifty(next: RequestHandler) extends RequestHandler(next){
  def denomination : BankNote = Fifty;
}
class RequestHandlerForTwenty(next: RequestHandler)extends RequestHandler(next){
  def denomination : BankNote = Twenty;
}
class RequestHandlerForTen(next: RequestHandler) extends RequestHandler(next){
  def denomination : BankNote = Ten; 
}
class RequestHandlerForFive(next: RequestHandler) extends RequestHandler(next){
  def denomination : BankNote = Five;
}

abstract class BankNote {
  def value : Int;
  override def toString : String = value.toString
}

// case objects rather than case class, immutable objects, should be singletons
case object Five    extends BankNote { def value = 5  }
case object Ten     extends BankNote { def value = 10 } 
case object Twenty  extends BankNote { def value = 20 }
case object Fifty   extends BankNote { def value = 50 }


object ChainOfResp {
  def main(args: Array[String]){
    val atm = new ATMMachine
    val list = atm.getAmount(235)
    println("The notes handed out by the ATM machine are:")
    // tweaking output to match that obtained in other languages
    println(list.reverse.mkString("[",", ","]"))  // format -> python, haskell
  }
}


