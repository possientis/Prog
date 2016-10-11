// Chain of Responsibility Design Pattern
import java.util.*;
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
class ATMMachine {

  // private data member representing the head of the chain of handlers
  private final RequestHandler _handler = RequestHandler.getHandlingChain();

  // main functionality
  public List<BankNote> getAmount(int amount){ 
    System.out.println("ATM machine: requesting amount of $" + amount);
    return _handler.handleRequest(amount);  // delegates request to chain 
  }

}

// This is the base class, uniting all request handlers into a common
// interface. This class in normally abstract (the whole point of the
// design pattern is dealing with multiple types of request).
abstract class RequestHandler {

  protected final RequestHandler _next; // successor

  // successor could be a mutable field with the appropriate setter
  public RequestHandler(RequestHandler next){ this._next = next;}

  // setting up the chain of responsibility. In our case, the request
  // handler responsible of the delivery of $50 notes will intervene
  // first, then pass on request to its successor
  public static RequestHandler getHandlingChain(){ 
    RequestHandler handler  = new RequestHandlerForFive(null);
    handler                 = new RequestHandlerForTen(handler);
    handler                 = new RequestHandlerForTwenty(handler); 
    handler                 = new RequestHandlerForFifty(handler);
    return handler;
  }

  // This is the main method of the class. It is often an abstract
  // method as the diffeent types of request handlers may have little
  // in common. In our case, all request handlers are similar and only
  // differ in the specific denomination of the bank note they deliver.
  // Such denominations are encoded in a virtual method.
  public List<BankNote> handleRequest(int amount){
    if(amount < 0)  { throw new IllegalArgumentException(); }
    if(amount == 0) { return new ArrayList<BankNote>(); } // empty list
    if(amount % 5 != 0){
      throw new IllegalArgumentException(
          "Requested amount should be multiple of $5");
    }

    // handleRequest logic is the same across all request handlers
    // in our case. However, this logic is parameterized by denomination
    // This is a case of mini-template method design pattern.
    BankNote denom = this.denomination();

    int value = denom.value();

    boolean addSingleNote = false;  // whether handler gives away note
    List<BankNote> list;  // will be returned after request completion

    if(amount >= value){
      list = handleRequest(amount - value);   // recursive call
      addSingleNote = true;                   // handler should give note
    } else {
      if(_next != null){
        list = _next.handleRequest(amount);   // passing on request
      } else {
        throw new IllegalStateException();    // chain badly set up
      }
    }
    // set of bank notes obtained by a mixture of recursive call and 
    // delegation of request to the next handler on the chain. We 
    // should not forget to add a single note if required.
    if(addSingleNote){ list.add(denom); }

    return list;
  }

  // This is what distinguishes one handdler from another
  // Hence the method is abstract
  public abstract BankNote denomination();
}

// delivers $50 notes
class RequestHandlerForFifty extends RequestHandler {
  public RequestHandlerForFifty(RequestHandler next){ super(next); }
  @Override 
  public BankNote denomination(){ return new Fifty(); }
}

// delivers $20 notes
class RequestHandlerForTwenty extends RequestHandler {
  public RequestHandlerForTwenty(RequestHandler next){ super(next); }
  @Override 
  public BankNote denomination(){ return new Twenty(); }
}

// delivers $10 notes
class RequestHandlerForTen extends RequestHandler {
  public RequestHandlerForTen(RequestHandler next){ super(next); }
  @Override 
  public BankNote denomination(){ return new Ten(); }
}

// delivers $5 notes
class RequestHandlerForFive extends RequestHandler {
  public RequestHandlerForFive(RequestHandler next){ super(next); }
  @Override 
  public BankNote denomination(){ return new Five(); }
}

// type BankNote could have been enum
abstract class BankNote {
  public abstract int value();
  @Override
  public String toString(){ return String.valueOf(value()); }
}

class Five extends BankNote{
  @Override public int value(){ return 5; } }

class Ten extends BankNote{
  @Override public int value(){ return 10; } }

class Twenty extends BankNote{
  @Override public int value(){ return 20; } }

class Fifty extends BankNote{
  @Override public int value(){ return 50; } }

public class ChainOfResp {
  public static void main(String[] args){
    ATMMachine atm = new ATMMachine();
    List<BankNote> list = atm.getAmount(235);
    System.out.println("The notes handed out by the ATM machine are:");
    System.out.println(list);
  }
}

