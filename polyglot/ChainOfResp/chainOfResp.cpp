// Chain of Responsibility Design Pattern
#include <iostream>
#include <vector>
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

typedef enum { Five=5, Ten=10, Twenty=20, Fifty=50 } BankNote;


// This is the base class, uniting all request handlers into a common
// interface. This class in normally abstract (the whole point of the
// design pattern is dealing with multiple types of request).
class RequestHandler {
  protected:
    const RequestHandler* const  _next; 
  public:
  virtual ~RequestHandler(){ if(_next != nullptr) delete _next; }
  RequestHandler(const RequestHandler* next):_next(next){}
  static const RequestHandler* getHandlingChain();
  std::vector<BankNote> handleRequest(int amount) const;
  virtual BankNote denomination() const =0;
};

// delivers $50 notes
class RequestHandlerForFifty : public RequestHandler {
  public:
  RequestHandlerForFifty(const RequestHandler* next): RequestHandler(next){} 
  BankNote denomination() const override { return Fifty; }
};

// delivers $20 notes
class RequestHandlerForTwenty : public RequestHandler {
  public:
  RequestHandlerForTwenty(const RequestHandler* next): RequestHandler(next){} 
  BankNote denomination() const override { return Twenty; }
};

// delivers $10 notes
class RequestHandlerForTen : public RequestHandler {
  public:
  RequestHandlerForTen(const RequestHandler* next): RequestHandler(next){} 
  BankNote denomination() const override { return Ten; }
};

// delivers $5 notes
class RequestHandlerForFive : public RequestHandler {
  public:
  RequestHandlerForFive(const RequestHandler* next): RequestHandler(next){} 
  BankNote denomination() const override { return Five; }
};


// RequestHandler implementation

const RequestHandler* RequestHandler::getHandlingChain(){
  const RequestHandler* handler = new RequestHandlerForFive(nullptr);
                        handler = new RequestHandlerForTen(handler);
                        handler = new RequestHandlerForTwenty(handler);
                        handler = new RequestHandlerForFifty(handler);
  return handler;
}

// This is the main method of the class. It is often an abstract
// method as the different types of request handlers may have little
// in common. In our case, all request handlers are similar and only
// differ in the specific denomination of the bank note they deliver.
// Such denominations are encoded in a virtual method.
std::vector<BankNote> RequestHandler::handleRequest(int amount) const {
  if(amount < 0) throw new std::exception();
  if(amount == 0){ std::vector<BankNote> nil; return nil; }
  if(amount % 5 != 0){ 
    std::cerr << "Requested amount should be multiple of $5\n";
    throw new std::exception();
  }
  
  // handleRequest logic is the same across all request handlers
  // in our case. However, this logic is parameterized by denomination
  // This is a case of mini-template method design pattern.
  BankNote denom = denomination();
  int value = (int) denom;
  bool addSingleNote = false;   // whether handler gives away note
  std::vector<BankNote> list;   // will be returned after request completion

  if(amount >= value){
    list = handleRequest(amount - value);     // recursive call
    addSingleNote = true;                     // handler should give note
  } else {
    if(_next != nullptr){
      list = _next->handleRequest(amount);    // passing on request
    } else {
      std::cerr << "Illegal state exception: chain is badly set up\n";
      throw new std::exception();
    }
  }
  // set of bank notes obtained by a mixture of recursive call and 
  // delegation of request to the next handler on the chain. We 
  // should not forget to add a single note if required.
  if(addSingleNote){ list.push_back(denom); } 

  return list;
}

// Our ATM machine only need to worry about the head of the chain of
// services, which it maintains as an internal data member. This machine
// has the ability to provide a set of bank notes from a desired amount

class ATMMachine {
  private:
  const RequestHandler* _handler;
  public:
  ~ATMMachine(){ delete _handler; }
  ATMMachine() : _handler(RequestHandler::getHandlingChain()) {}
  std::vector<BankNote> getAmount(int amount);  // main functionality
};

// ATMMachine implementation

std::vector<BankNote> ATMMachine::getAmount(int amount){
  std::cout << "ATM machine: requesting amount of $" << amount << std::endl;
  return _handler->handleRequest(amount); // delegates request to chain
}

std::ostream& operator<<(std::ostream& s, std::vector<BankNote> v){
  s << "[";
  bool start = true;
  for(auto p = v.begin(); p != v.end(); ++p){
    if(start){
      start = false;
    } else {
      s << ", ";
    }
    s << (int) *p;
  }
  s << "]";
  return s;
}


int main(){

  ATMMachine atm;
  std::vector<BankNote> list = atm.getAmount(235);
  std::cout << "The notes handed out by the ATM machine are:\n";
  std::cout << list << std::endl;

  return 0;
}
