// Chain of Responsibility Design Pattern
#include <stdio.h>
#include <assert.h>
#include <malloc.h>
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

// 'NullNote' will be used to terminate variable length arrays of BankNote
typedef enum { Five=5, Ten=10, Twenty=20, Fifty=50, NullNote=0 } BankNote;

typedef struct RequestHandler_  RequestHandler;
typedef struct ATMMachine_      ATMMachine;

/******************************************************************************/
/*                              Memory log                                    */
/******************************************************************************/

// basic safety scheme against memory leaks
long chainOfResp_log(const char* message, const void* address){
  static long memory_check = 0L;
  // Set_log(NULL,NULL) returns current memory_check
  if((message == NULL) && (address == NULL)) return memory_check;
  assert(message != NULL);
  assert(address != NULL);
  // message should contain %lx so fprintf expects third 'address' argument
//  fprintf(stderr, message, address);  // uncomment this line when needed
  memory_check ^= (long) address;     // xor-ing address as sanity check
//  fprintf(stderr, "checksum = %ld\n", memory_check);
  return 0L;
}

int chainOfResp_hasMemoryLeak(){
  return chainOfResp_log(NULL, NULL) != 0L;
}

/******************************************************************************/
/*                              RequestHandler                                */
/******************************************************************************/

struct RequestHandler_ {
  int refcount;
  BankNote denomination;
  RequestHandler* next;
}; 

RequestHandler* RequestHandler_new(
  RequestHandler* next, BankNote denomination){
  RequestHandler* ptr = (RequestHandler*) malloc(sizeof(RequestHandler));
  assert(ptr != NULL);
  chainOfResp_log("Allocating new RequestHandler %lx\n", ptr);
  ptr->refcount = 1;
  ptr->denomination = denomination;
  ptr->next = next;
}

RequestHandler* RequestHandler_copy(RequestHandler* self){
  assert(self != NULL);
  self->refcount++;
  chainOfResp_log("Making copy of RequestHandler %lx\n", self);
  return self;
}

void RequestHandler_delete(RequestHandler* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    if(self->next != NULL) RequestHandler_delete(self->next); // we own it
    self->next = NULL;
    chainOfResp_log("Deallocating existing RequestHandler %lx\n", self);
    free(self);
  } else {
    chainOfResp_log("Deleting copy of RequestHander %lx\n", self);
  }
}

// delivers $50 notes
RequestHandler* RequestHandlerForFifty_new(RequestHandler* next){
  return RequestHandler_new(next, Fifty);
}

// delivers $20 notes
RequestHandler* RequestHandlerForTwenty_new(RequestHandler* next){
  return RequestHandler_new(next, Twenty);
}

// delivers $10 notes
RequestHandler* RequestHandlerForTen_new(RequestHandler* next){
  return RequestHandler_new(next, Ten);
}

// delivers $5 notes
RequestHandler* RequestHandlerForFive_new(RequestHandler* next){
  return RequestHandler_new(next, Five);
}

RequestHandler* RequestHandler_getHandlingChain(){
  RequestHandler* handler = RequestHandlerForFive_new(NULL);
                  handler = RequestHandlerForTen_new(handler);
                  handler = RequestHandlerForTwenty_new(handler);
                  handler = RequestHandlerForFifty_new(handler);
                  return handler;
}


// Array of bank notes returned via buffer which is the caller's responsibility 
// size argument is the size of buffer, which should be at least 1 + the number
// of notes corresponding to 'amount', to allow for the final 'NullNote'.
// return 0 on success, -1 on failure
int RequestHandler_handleRequest(
    RequestHandler* self, int amount, BankNote* buffer, size_t size){
  if(self == NULL){
    fprintf(stderr, "RequestHandler_handleRequest: NULL object error\n");
    return -1;
  }
  if(buffer == NULL){
    fprintf(stderr, "RequestHandler_handlerRequest: buffer is NULL error\n");
    return -1;
  }
  if(size <= 0){
    fprintf(stderr, "RequestHandler_handlerRequest: buffer size should be > 0\n");
    return -1;
  }
  if(amount < 0){
    fprintf(stderr,"RequestHandler_handleRequest: amount should be >= 0\n");
    return -1;
  }
  if(amount % 5 != 0){
    fprintf(stderr, 
        "RequestHandler_handleRequest: amount should be multiple of 5\n");
    return -1;
  }
  if(amount == 0){
    buffer[0] = NullNote; // returning empty list
    return 0;
  }

  int value = (int) self->denomination;

  if(amount >= value){  // need to give away note
    if(size <= 1){
      fprintf(stderr, "RequestHandler_handleRequest: buffer too small\n");
      return -1;
    }
    buffer[0] = self->denomination; // give away note
    buffer[1] = NullNote;           // temporary end of list
    buffer++; size--;
    return RequestHandler_handleRequest(self, amount - value, buffer, size);
  }

  // request handler cannot handle request, delegating to successor
  if(self->next != NULL){
    return RequestHandler_handleRequest(self->next, amount, buffer, size);
  }

  // no successor was found
  fprintf(stderr, "RequestHandler_handleRequest: chain is badly set up\n");
  return -1;
}


int RequestHandler_test(){
  // basic new/copy/test
  RequestHandler *h1 = RequestHandler_new(NULL, Five);
  RequestHandler *h2 = RequestHandler_copy(h1);
  RequestHandler_delete(h1);
  RequestHandler_delete(h2);
  assert(!chainOfResp_hasMemoryLeak());
  // chain
  h1 = RequestHandler_getHandlingChain();
  assert(h1 != NULL);
  assert(h1->denomination = Fifty);
  assert(h1->next != NULL);
  assert(h1->next->denomination = Twenty);
  assert(h1->next->next != NULL);
  assert(h1->next->next->denomination = Ten);
  assert(h1->next->next->next != NULL);
  assert(h1->next->next->next->denomination = Five);
  assert(h1->next->next->next->next == NULL);
  RequestHandler_delete(h1);
  assert(!chainOfResp_hasMemoryLeak());
  return 0;
}



/******************************************************************************/
/*                              ATMMachine                                    */
/******************************************************************************/

struct ATMMachine_ {
  RequestHandler *handler;
};

void ATMMachine_initialize(ATMMachine* self){
  assert(self != NULL);
  self->handler = RequestHandler_getHandlingChain();
  assert(self->handler != NULL);
}

void ATMMachine_destroy(ATMMachine* self){
  assert(self != NULL);
  assert(self->handler != NULL);
  RequestHandler_delete(self->handler);
  self->handler = NULL;
}

int ATMMachine_getAmount(
    ATMMachine* self, int amount, BankNote* buffer, size_t size){
  if(self == NULL){
    fprintf(stderr, "ATMMachine_getAmount: Null object error\n");
    return -1;
  }
  if(self->handler == NULL){
    fprintf(stderr, "ATMMachine_getAmount: no handler found\n");
    return -1;
  }
  printf("ATM machine: requesting amount of $%d\n", amount);
  return RequestHandler_handleRequest(self->handler, amount, buffer, size);
}

void ATMMachine_printList(BankNote* list){
  assert(list != NULL);
  printf("[");
  int start = 1;
  while(*list != NullNote){
    if(start){
      start =0;
    } else {
      printf(", ");
    }
    printf("%d", (int) *list);
    list++;
  }
  printf("]");
}

void ATMMachine_reverseList(BankNote* list){
  assert(list != NULL);
  BankNote* start = list;
  BankNote* end = list;
  while(*end != NullNote) end++;
  end--;  // end points to last element unless list is empty
  while(start < end){
    BankNote temp = *start;
    *start = *end;
    *end = temp;
    start++;
    end--;
  }
}


int main(){
//  RequestHandler_test();

  BankNote buffer[16];

  ATMMachine atm;
  ATMMachine_initialize(&atm);
  int reqResult = ATMMachine_getAmount(&atm, 235, buffer, 16);
  assert(reqResult == 0);
  ATMMachine_reverseList(buffer); // consistency of output with other languages
  printf("The notes handed out by the ATM machine are:\n");
  ATMMachine_printList(buffer);
  printf("\n");
  ATMMachine_destroy(&atm);
  assert(!chainOfResp_hasMemoryLeak());
  return 0;
}


