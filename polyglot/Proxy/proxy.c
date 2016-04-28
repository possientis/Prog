// Proxy Design Pattern
#include <stdio.h>
#include <malloc.h>
#include <assert.h>

// This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
// https://www.youtube.com/watch?v=XvbDqLrnkmA

// A proxy is a class which functions as an interface to something else

// There are three participants to the proxy design pattern:
//
// 1. subject
// 2. real subject
// 3. proxy
//

// The subject is the common interface between the real object and proxy
// the real object is that which the proxy is meant to be substituted for

typedef struct ComponentPrice_vTable_   ComponentPrice_vTable;
typedef struct ComponentPrice_          ComponentPrice;
typedef struct Server_                  Server;
typedef enum { CPU=0, RAM=1, SSD=2 }          Request;

const char* Request_toString[3] = {"CPU", "RAM", "SSD"}; 

/******************************************************************************/
/*                              Memory log                                    */
/******************************************************************************/

// basic safety scheme against memory leaks
long ComponentPrice_log(const char* message, const void* address){
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

int ComponentPrice_hasMemoryLeak(){
  return ComponentPrice_log(NULL, NULL) != 0L;
}

/******************************************************************************/
/*                           Virtual tables                                   */
/******************************************************************************/

struct ComponentPrice_vTable_ {
  int    refcount;
  double (*cpu_price)(ComponentPrice* self);
  double (*ram_price)(ComponentPrice* self);
  double (*ssd_price)(ComponentPrice* self);
};


ComponentPrice_vTable *ComponentPrice_vTable_copy(ComponentPrice_vTable* self){
  assert(self != NULL);
  ComponentPrice_log("Making copy of ComponentPrice virtual table %lx\n", self);
  assert(self->refcount > 0);
  self->refcount++;
  return self;
}

ComponentPrice_vTable *ComponentPrice_vTable_new(){
  ComponentPrice_vTable* ptr = 
    (ComponentPrice_vTable*) malloc(sizeof(ComponentPrice_vTable)); 
  assert(ptr != NULL);
  ComponentPrice_log("Allocating new ComponentPrice virtual table %lx\n", ptr);
  ptr->refcount = 1;
  ptr->cpu_price = NULL;
  ptr->ram_price = NULL;
  ptr->ssd_price = NULL;
  return ptr;
}

void ComponentPrice_vTable_delete(ComponentPrice_vTable* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){  // need to free memory
    ComponentPrice_log("Deallocating ComponentPrice virtual table %lx\n", self);
    self->cpu_price = NULL;   // statically allocated, no clean up required
    self->ram_price = NULL;   //  " 
    self->ssd_price = NULL;   //  "
    free(self);
  } else {
    ComponentPrice_log(
        "Deleting copy of ComponentPrice virtual table %lx\n", self);
  }
}



/******************************************************************************/
/*                        ComponentPrice virtual table                        */
/******************************************************************************/

double _ComponentPrice_cpu_price(ComponentPrice* self){
  assert(self != NULL);
  fprintf(stderr,"ComponentPrice::cpu_price is not implemented\n");
  return 0;
} 

double _ComponentPrice_ram_price(ComponentPrice* self){
  assert(self != NULL);
  fprintf(stderr,"ComponentPrice::ram_price is not implemented\n");
  return 0;
}

double _ComponentPrice_ssd_price(ComponentPrice* self){
  assert(self != NULL);
  fprintf(stderr,"ComponentPrice::ssd_price is not implemented\n");
  return 0;
}

ComponentPrice_vTable* ComponentPrice_VT_new(){
  ComponentPrice_vTable* ptr = ComponentPrice_vTable_new();
  assert(ptr != NULL);
  ptr->cpu_price = _ComponentPrice_cpu_price;
  ptr->ram_price = _ComponentPrice_ram_price;
  ptr->ssd_price = _ComponentPrice_ssd_price;
  return ptr;
}

// returns single virtual table instance, unless resetInstanceFlag = true
// in which case returns NULL, after deleting instance
ComponentPrice_vTable* ComponentPrice_VT_instance(int resetInstanceFlag){
  static ComponentPrice_vTable* instance = NULL;
  if(resetInstanceFlag){  // deleting instance
    if(instance != NULL){
    ComponentPrice_vTable_delete(instance);
    instance = NULL;
    return NULL;
    }
  } else {
    if(instance == NULL){
      instance = ComponentPrice_VT_new();
    }
    return instance;
  }
}

/******************************************************************************/
/*                        StoredComponentPrice virtual table                  */
/******************************************************************************/

double _StoredComponentPrice_cpu_price(ComponentPrice* self){
  assert(self != NULL);
  return 250.0;
} 

double _StoredComponentPrice_ram_price(ComponentPrice* self){
  assert(self != NULL);
  return 32.0;
}

double _StoredComponentPrice_ssd_price(ComponentPrice* self){
  assert(self != NULL);
  return 225.0;
}

ComponentPrice_vTable* StoredComponentPrice_VT_new(){
  ComponentPrice_vTable* ptr = ComponentPrice_vTable_new();
  assert(ptr != NULL);
  ptr->cpu_price = _StoredComponentPrice_cpu_price;
  ptr->ram_price = _StoredComponentPrice_ram_price;
  ptr->ssd_price = _StoredComponentPrice_ssd_price;
  return ptr;
}

// returns single virtual table instance, unless resetInstanceFlag = 1
// in which case returns NULL, after deleting instance
ComponentPrice_vTable* StoredComponentPrice_VT_instance(int resetInstanceFlag){
  static ComponentPrice_vTable* instance = NULL;
  if(resetInstanceFlag){  // deleting instance
    if(instance != NULL){
    ComponentPrice_vTable_delete(instance);
    instance = NULL;
    return NULL;
    }
  } else {
    if(instance == NULL){
      instance = StoredComponentPrice_VT_new();
    }
    return instance;
  }
}

/******************************************************************************/
/*                        ProxyComponentPrice virtual table                   */
/******************************************************************************/

double requestFromServer(Request);

double _ProxyComponentPrice_cpu_price(ComponentPrice* self){
  assert(self != NULL);
  return requestFromServer(CPU);
} 

double _ProxyComponentPrice_ram_price(ComponentPrice* self){
  assert(self != NULL);
  return requestFromServer(RAM);
}

double _ProxyComponentPrice_ssd_price(ComponentPrice* self){
  assert(self != NULL);
  return requestFromServer(SSD);
}

ComponentPrice_vTable* ProxyComponentPrice_VT_new(){
  ComponentPrice_vTable* ptr = ComponentPrice_vTable_new();
  assert(ptr != NULL);
  ptr->cpu_price = _ProxyComponentPrice_cpu_price;
  ptr->ram_price = _ProxyComponentPrice_ram_price;
  ptr->ssd_price = _ProxyComponentPrice_ssd_price;
  return ptr;
}

// returns single virtual table instance, unless resetInstanceFlag = 1
// in which case returns NULL, after deleting instance
ComponentPrice_vTable* ProxyComponentPrice_VT_instance(int resetInstanceFlag){
  static ComponentPrice_vTable* instance = NULL;
  if(resetInstanceFlag){  // deleting instance
    if(instance != NULL){
    ComponentPrice_vTable_delete(instance);
    instance = NULL;
    return NULL;
    }
  } else {
    if(instance == NULL){
      instance = ProxyComponentPrice_VT_new();
    }
    return instance;
  }
}

/******************************************************************************/
/*                           Testing virtual tables                           */
/******************************************************************************/



int ComponentPrice_vTable_test(){
  // basic new/copy/delete test
  fprintf(stderr,"\nvirtual table ...\n");
  ComponentPrice_vTable* vt1 = ComponentPrice_vTable_new();
  ComponentPrice_vTable* vt2 = ComponentPrice_vTable_copy(vt1);
  ComponentPrice_vTable_delete(vt1);
  ComponentPrice_vTable_delete(vt2);
  assert(!ComponentPrice_hasMemoryLeak());
  // testing ComponentPrice virtual table
  fprintf(stderr,"\nComponentPrice virtual table ...\n");
  vt1 = ComponentPrice_VT_new();
  assert(vt1 != NULL);
  assert(vt1->cpu_price == _ComponentPrice_cpu_price);
  assert(vt1->ram_price == _ComponentPrice_ram_price);
  assert(vt1->ssd_price == _ComponentPrice_ssd_price);
  ComponentPrice_vTable_delete(vt1);
  assert(!ComponentPrice_hasMemoryLeak());
  // testing ComponentPrice virtual table instance
  vt1 = ComponentPrice_VT_instance(0);  // resetInstanceFlag = false
  assert(vt1 != NULL);
  assert(vt1->cpu_price == _ComponentPrice_cpu_price);
  assert(vt1->ram_price == _ComponentPrice_ram_price);
  assert(vt1->ssd_price == _ComponentPrice_ssd_price);
  vt2 = ComponentPrice_VT_instance(0);  // resetInstanceFlag = false
  assert(vt1 == vt2);
  ComponentPrice_VT_instance(1);        // resetInstanceFlag = true
  assert(!ComponentPrice_hasMemoryLeak());
  // testing StoredComponentPrice virtual table
  fprintf(stderr,"\nStoredComponentPrice virtual table ...\n");
  vt1 = StoredComponentPrice_VT_new();
  assert(vt1 != NULL);
  assert(vt1->cpu_price == _StoredComponentPrice_cpu_price);
  assert(vt1->ram_price == _StoredComponentPrice_ram_price);
  assert(vt1->ssd_price == _StoredComponentPrice_ssd_price);
  ComponentPrice_vTable_delete(vt1);
  assert(!ComponentPrice_hasMemoryLeak());
  // testing ComponentPrice virtual table instance
  vt1 = StoredComponentPrice_VT_instance(0);  // resetInstanceFlag = false
  assert(vt1 != NULL);
  assert(vt1->cpu_price == _StoredComponentPrice_cpu_price);
  assert(vt1->ram_price == _StoredComponentPrice_ram_price);
  assert(vt1->ssd_price == _StoredComponentPrice_ssd_price);
  vt2 = StoredComponentPrice_VT_instance(0);  // resetInstanceFlag = false
  assert(vt1 == vt2);
  StoredComponentPrice_VT_instance(1);        // resetInstanceFlag = true
  assert(!ComponentPrice_hasMemoryLeak());
  // testing ProxyComponentPrice virtual table
  fprintf(stderr,"\nProxyComponentPrice virtual table ...\n");
  vt1 = ProxyComponentPrice_VT_new();
  assert(vt1 != NULL);
  assert(vt1->cpu_price == _ProxyComponentPrice_cpu_price);
  assert(vt1->ram_price == _ProxyComponentPrice_ram_price);
  assert(vt1->ssd_price == _ProxyComponentPrice_ssd_price);
  ComponentPrice_vTable_delete(vt1);
  assert(!ComponentPrice_hasMemoryLeak());
  // testing ComponentPrice virtual table instance
  vt1 = ProxyComponentPrice_VT_instance(0);  // resetInstanceFlag = false
  assert(vt1 != NULL);
  assert(vt1->cpu_price == _ProxyComponentPrice_cpu_price);
  assert(vt1->ram_price == _ProxyComponentPrice_ram_price);
  assert(vt1->ssd_price == _ProxyComponentPrice_ssd_price);
  vt2 = ProxyComponentPrice_VT_instance(0);  // resetInstanceFlag = false
  assert(vt1 == vt2);
  ProxyComponentPrice_VT_instance(1);        // resetInstanceFlag = true
  assert(!ComponentPrice_hasMemoryLeak());

  return 0;
}


/******************************************************************************/
/*                              ComponentPrice                                */
/******************************************************************************/

// this is the subject
struct ComponentPrice_ {
  int refcount;
  ComponentPrice_vTable* vTable;
};



ComponentPrice* ComponentPrice_new(ComponentPrice_vTable* table){
  assert(table != NULL);
  ComponentPrice* ptr = (ComponentPrice*) malloc(sizeof(ComponentPrice));
  assert(ptr != NULL);
  ComponentPrice_log("Allocating new ComponentPrice object %lx\n", ptr);
  ptr->refcount = 1;
  ptr->vTable   = table;
  return ptr;
}

ComponentPrice* ComponentPrice_copy(ComponentPrice* self){
  assert(self != NULL);
  ComponentPrice_log("Making copy of ComponentPrice object %lx\n", self);
  self->refcount++;
  return self;
}

void ComponentPrice_delete(ComponentPrice* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){  // need to deallocate
    ComponentPrice_log("Deallocating ComponentPrice object %lx\n", self);
    self->vTable = NULL;  // we do not have ownership of virtual table
    free(self);
  } else {
    ComponentPrice_log("Deleting copy of ComponentPrice object %lx\n", self);
  }
}

// this is the real subject
ComponentPrice* StoredComponentPrice_new(){
  ComponentPrice_vTable* table = StoredComponentPrice_VT_instance(0); // reset=no
  assert(table != NULL);
  ComponentPrice* object = ComponentPrice_new(table);
  assert(object != NULL);
  return object;
}

//this is the proxy
ComponentPrice* ProxyComponentPrice_new(){
  ComponentPrice_vTable* table = ProxyComponentPrice_VT_instance(0); // reset=no
  assert(table != NULL);
  ComponentPrice* object = ComponentPrice_new(table);
  assert(object != NULL);
  return object;
}

double ComponentPrice_cpu_price(ComponentPrice *self){
  assert(self != NULL);
  assert(self->vTable != NULL);
  assert(self->vTable->cpu_price != NULL);
  return self->vTable->cpu_price(self);
}

double ComponentPrice_ram_price(ComponentPrice *self){
  assert(self != NULL);
  assert(self->vTable != NULL);
  assert(self->vTable->ram_price != NULL);
  return self->vTable->ram_price(self);
}

double ComponentPrice_ssd_price(ComponentPrice *self){
  assert(self != NULL);
  assert(self->vTable != NULL);
  assert(self->vTable->ssd_price != NULL);
  return self->vTable->ssd_price(self);
}


// cleaning up allocated virtual tables
void ComponentPrice_cleanup(){
  ComponentPrice_VT_instance(1);        // resetInstanceFlag = true
  StoredComponentPrice_VT_instance(1);  // resetInstanceFlag = true
  ProxyComponentPrice_VT_instance(1);   // resetInstanceFlag = true
}



/******************************************************************************/
/*                         Testing ComponentPrice                             */
/******************************************************************************/
void Server_start();
void Server_stop();

int ComponentPrice_test(){
  // basic new/copy/delete test
  fprintf(stderr,"\nComponentPrice...\n");
  ComponentPrice  *p1 = ComponentPrice_new(ComponentPrice_VT_instance(0));
  ComponentPrice  *p2 = ComponentPrice_new(StoredComponentPrice_VT_instance(0));
  ComponentPrice  *p3 = ComponentPrice_new(ProxyComponentPrice_VT_instance(0));
  ComponentPrice  *p4 = ComponentPrice_copy(p1);
  ComponentPrice_delete(p1);
  ComponentPrice_delete(p2);
  ComponentPrice_delete(p3);
  ComponentPrice_delete(p4);
  ComponentPrice_cleanup();
  assert(!ComponentPrice_hasMemoryLeak());
  // testing StoredComponentPrice
  fprintf(stderr,"\nStoredComponentPrice...\n");
  p1 = StoredComponentPrice_new();
  assert(p1 != NULL);
  assert(p1->vTable == StoredComponentPrice_VT_instance(0));
  assert(ComponentPrice_cpu_price(p1) == 250.0);
  assert(ComponentPrice_ram_price(p1) == 32.0);
  assert(ComponentPrice_ssd_price(p1) == 225.0);
  ComponentPrice_delete(p1);
  ComponentPrice_cleanup();
  assert(!ComponentPrice_hasMemoryLeak());
  // testing ProxyComponentPrice
  fprintf(stderr,"\nProxyComponentPrice...\n");
  Server_start();
  p1 = ProxyComponentPrice_new();
  assert(p1 != NULL);
  assert(p1->vTable == ProxyComponentPrice_VT_instance(0));
  assert(ComponentPrice_cpu_price(p1) == 250.0);
  assert(ComponentPrice_ram_price(p1) == 32.0);
  assert(ComponentPrice_ssd_price(p1) == 225.0);
  ComponentPrice_delete(p1);
  ComponentPrice_cleanup();
  Server_stop();
  assert(!ComponentPrice_hasMemoryLeak());


  return 0;
}


/******************************************************************************/
/*                                  Server                                    */
/******************************************************************************/

struct Server_ {
  int refcount;
};

Server* Server_new(){
  Server* ptr = (Server*) malloc(sizeof(Server));
  assert(ptr != NULL);
  ComponentPrice_log("Allocating new server %lx\n", ptr);
  ptr->refcount = 1;
  return ptr;
}

Server* Server_copy(Server* self){
  assert(self != NULL);
  ComponentPrice_log("Making copy of server %lx\n", self);
  self->refcount++;
  return self;
}

void Server_delete(Server* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    ComponentPrice_log("Deallocating existing server %lx\n", self);
    free(self);
  } else {
    ComponentPrice_log("Deleting copy of server %lx\n", self);
  }
}


Server* Server_instance(int resetInstanceFlag){
  static Server* instance = NULL;
  if(resetInstanceFlag){
    if(instance != NULL){
      Server_delete(instance);
      instance = NULL;
      return NULL;
    }
  } else {
    if(instance == NULL){
      instance = Server_new();
    }
    return instance;
  }
}


void Server_start(){
  Server_instance(0);
  printf("Component price server running, awaiting request\n");
}

void Server_stop(){
  Server_instance(1);
}

double Server_sendRequest(Server* server, Request request){
  assert(server != NULL);
  printf("Server receiving request for %s price\n", Request_toString[request]);
  // In our example, server uses real subject
  ComponentPrice* component = StoredComponentPrice_new(); // real subject
  printf("Server responding to request for %s price\n", Request_toString[request]);
  int result;
  switch(request){
    case CPU:
      result = ComponentPrice_cpu_price(component);
      break;
    case RAM:
      result = ComponentPrice_ram_price(component);
      break;
    case SSD:
      result = ComponentPrice_ssd_price(component);
      break;
    default:
      fprintf(stderr,"Server: unexpected error while processing request\n");
      result = 0;
      break;
  }
  ComponentPrice_delete(component);
  return result;
}


double requestFromServer(Request request){
  return Server_sendRequest(Server_instance(0), request);
}

int Server_test(){
  // basic new/copy/delete test
  fprintf(stderr,"\nServer...\n");
  Server *s1 = Server_new();
  Server *s2 = Server_copy(s1);
  Server_delete(s1);
  Server_delete(s2);
  assert(!ComponentPrice_hasMemoryLeak());
  // server instance
  s1 = Server_instance(0);  // resetInstance = false
  s2 = Server_instance(0);
  assert(s1 == s2);
  Server_instance(1);       // resetInstance = true
  assert(!ComponentPrice_hasMemoryLeak());
  // start/stop
  Server_start();
  Server_stop();
  assert(!ComponentPrice_hasMemoryLeak());
  return 0;
}

int proxy_test(){
  ComponentPrice_vTable_test();
  ComponentPrice_test();
  Server_test();
  return 0;
}

int main(){
  Server_start();
  // we can use proxy as if it was real, making client code a lot simpler
  ComponentPrice* prices = ProxyComponentPrice_new();
  double cpu = ComponentPrice_cpu_price(prices);
  double ram = ComponentPrice_ram_price(prices);
  double ssd = ComponentPrice_ssd_price(prices);
  printf("The CPU price is %0.1f\n", cpu);
  printf("The RAM price is %0.1f\n", ram);
  printf("The SSD price is %0.1f\n", ssd);


  // heap cleanup
  ComponentPrice_delete(prices);
  ComponentPrice_cleanup(); // virtual tables
  Server_stop();            // server cleanup
  assert(!ComponentPrice_hasMemoryLeak());
  return 0;
}


