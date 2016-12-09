// Chain of Responsibility Design Pattern
using System;
using System.Collections.Generic; 
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
  private readonly RequestHandler _handler = RequestHandler.GetHandlingChain();

  // main functionality
  public IList<BankNote> GetAmount(int amount){ 
    Console.WriteLine("ATM machine: requesting amount of ${0}", amount);
    return _handler.HandleRequest(amount);  // delegates request to chain 
  }
}

// This is the base class, uniting all request handlers into a common
// interface. This class in normally abstract (the whole point of the
// design pattern is dealing with multiple types of request).
abstract class RequestHandler {

  protected readonly RequestHandler _next; // successor

  // successor could be a mutable field with the appropriate setter
  public RequestHandler(RequestHandler next){ this._next = next;}

  // setting up the chain of responsibility. In our case, the request
  // handler responsible of the delivery of $50 notes will intervene
  // first, then pass on request to its successor
  public static RequestHandler GetHandlingChain(){ 
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
  public IList<BankNote> HandleRequest(int amount){
    if(amount < 0)  { throw new ArgumentException(); }
    if(amount == 0) { return new List<BankNote>(); } // empty list
    if(amount % 5 != 0){
      throw new ArgumentException("Requested amount should be multiple of $5");
    }

    // handleRequest logic is the same across all request handlers
    // in our case. However, this logic is parameterized by denomination
    // This is a case of mini-template method design pattern.
    BankNote denom = this.Denomination();

    int noteValue = denom.Value;

    bool addSingleNote = false;  // whether handler gives away note
    IList<BankNote> list;         // will be returned after request completion

    if(amount >= noteValue){
      list = HandleRequest(amount - noteValue); // recursive call
      addSingleNote = true;                     // handler should give note
    } else {
      if(_next != null){
        list = _next.HandleRequest(amount);     // passing on request
      } else {
        throw new Exception("Illegal state");   // chain badly set up
      }
    }
    // set of bank notes obtained by a mixture of recursive call and 
    // delegation of request to the next handler on the chain. We 
    // should not forget to add a single note if required.
    if(addSingleNote){ list.Add(denom); }

    return list;
  }

  // This is what distinguishes one handdler from another
  // Hence the method is abstract
  public abstract BankNote Denomination();
}

// delivers $50 notes
class RequestHandlerForFifty : RequestHandler {
  public RequestHandlerForFifty(RequestHandler next) : base(next){}
  public override BankNote Denomination(){ return new Fifty(); }
}

// delivers $20 notes
class RequestHandlerForTwenty : RequestHandler {
  public RequestHandlerForTwenty(RequestHandler next) : base(next){}
  public override BankNote Denomination(){ return new Twenty(); }
}

// delivers $10 notes
class RequestHandlerForTen : RequestHandler {
  public RequestHandlerForTen(RequestHandler next) : base(next){}
  public override BankNote Denomination(){ return new Ten(); }
}

// delivers $5 notes
class RequestHandlerForFive : RequestHandler {
  public RequestHandlerForFive(RequestHandler next) : base(next){}
  public override BankNote Denomination(){ return new Five(); }
}

// type BankNote could have been Enum
abstract class BankNote {
  public abstract int Value { get; }
  public override string ToString(){ return String.Format("{0}",Value); } 
  public static void PrintList(IList<BankNote> list){
    bool isStart = true;
    Console.Write("[");
    foreach(BankNote note in list){
      if(isStart){
        isStart = false;
      } else {
        Console.Write(", ");
      }
      Console.Write(note);
    }
    Console.Write("]");
  }
}

class Five : BankNote {
  public override int Value { get { return 5; } } 
}

class Ten : BankNote {
  public override int Value { get { return 10; } } 
}

class Twenty : BankNote {
  public override int Value { get { return 20; } } 
}

class Fifty : BankNote {
  public override int Value { get { return 50; } } 
}

public class ChainOfResp {
  public static void Main(string[] args){
    ATMMachine atm = new ATMMachine();
    IList<BankNote> list = atm.GetAmount(235);
    Console.WriteLine("The notes handed out by the ATM machine are:");
    BankNote.PrintList(list);
    Console.WriteLine("");
  }
}
