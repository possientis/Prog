// dict.c
#include "dict.h"
#include "link.h"
#include <malloc.h>
#include <assert.h>

// basic safety scheme against memory leaks
long Dictionary_log(const char* message, const void* address){
  static long memory_check = 0L;
  // Dictionary_log(NULL,NULL) returns current memory_check
  if((message == NULL) && (address == NULL)) return memory_check;
  assert(message != NULL);
  assert(address != NULL);
  // message should contain %lx so fprintf expects third 'address' argument
  //fprintf(stderr, message, address);  // uncomment this line when needed
  memory_check ^= (long) address;     // xor-ing address as sanity check
  return 0L;
}

int Dictionary_hasMemoryLeak(){
  return (Dictionary_log(NULL, NULL) != 0L ? 1 : 0);
}

typedef struct Pair_ Pair;
struct Pair_ {
  int key;
  const void* value;
};


struct Dictionary_ {
  int           refcount;     // reference count to Dictionary object
  int           num;          // number of entries
  int           size;         // allocated space
  int           isMemEnabled; // flag enabling memory allocation or deallocation
  Link**        data;         // vector of Link-ed list
};


Dictionary* Dictionary_new(){
#define DICT_C_INITIAL_SIZE 4
  Dictionary* ptr = (Dictionary*) malloc(sizeof(Dictionary));
  assert(ptr != NULL);
  Dictionary_log("Allocating new dictionary %lx\n", ptr);
  Link** data = (Link**) malloc(DICT_C_INITIAL_SIZE*sizeof(Link*));
  assert(data != NULL);
  Dictionary_log("Allocating data array %lx\n", data);
  int i;
  for(i = 0; i < DICT_C_INITIAL_SIZE; ++i){
    data[i] = NULL;
  }
  ptr->refcount     = 1;    // returned pointer is unique existing reference
  ptr->num          = 0;    // created dictionary is empty
  ptr->size         = DICT_C_INITIAL_SIZE; 
  ptr->isMemEnabled = 1;    // allows further memory allocation or deallocation
  ptr->data         = data;
}

Dictionary* Dictionary_copy(Dictionary* self){
  assert(self != NULL);
  Dictionary_log("Making copy of dictionary %lx\n", self);
  self->refcount++;
  return self;
}

void Dictionary_delete(Dictionary* self){
  assert(self != NULL);
  self->refcount--;
  if(self->refcount == 0){
    assert(self->data != NULL);
    int i;
    for(i = 0; i < self->size; ++i){
      if(self->data[i] != NULL){  // hash table has Link-ed list entry for hash i
        Link_delete(self->data[i]);
      } 
    }
    Dictionary_log("Deallocating data array %lx\n", self->data);
    free(self->data);
    self->num           = 0;
    self->size          = 0;
    self->isMemEnabled  = 0;
    self->data          = NULL;
    Dictionary_log("Deallocating dictionary %lx\n", self);
    free(self);
  } else {
    Dictionary_log("Deleting copy of dictionary %lx\n", self);
  }
}

Pair *Dictionary_tempVector(Dictionary* self){
  assert(self != NULL);
  Pair* ptr = (Pair*) malloc(self->num*sizeof(Pair));
  assert(ptr != NULL);
  Dictionary_log("Allocating new temporary vector %lx\n", ptr);
  int index = 0;
  int i;
  assert(self->data != NULL);
  for(i = 0; i < self->size; ++i){
    if(self->data[i] != NULL){
      LinkIter* iter = LinkIter_new(self->data[i]);
      while(LinkIter_hasNext(iter)){
        LinkIter_moveNext(iter);
        ptr[index].key    = LinkIter_key(iter);
        ptr[index].value  = LinkIter_value(iter); 
        ++index;
      }
      LinkIter_delete(iter);
    }
  }
  assert(index == self->num);
  return ptr;
}

void Dictionary_debug(Dictionary* self){
  assert(self != NULL);
  printf("----------------------------\n");
  printf("Hash table debug:\n");
  printf("Allocated table size: %d\n", self->size);
  printf("Number of elements: %d\n\n", self->num);
  printf("Hash table entries as follows:\n");
  int i;
  for(i = 0; i < self->size; ++i){
    printf("entry %d: ", i);
    if(self->data[i] == NULL){
      printf("NULL");
    } else {
      LinkIter* iter = LinkIter_new(self->data[i]);
      while(LinkIter_hasNext(iter)){
        LinkIter_moveNext(iter);
        printf("key = %d: value = %lx\t", 
            LinkIter_key(iter), LinkIter_value(iter));
      }
      LinkIter_delete(iter);
    }
    printf("\n");
  }
  printf("Vector of elements as follows:\n");
  Pair *temp = Dictionary_tempVector(self);
  for(i = 0; i < self->num; ++i){
    printf("%d:\tkey = %d\tvalue = %lx\n", i, temp[i].key, temp[i].value);
  }
  Dictionary_log("Deallocating temporary vector %lx\n", temp); 
  free(temp);

  printf("----------------------------\n");
}
    
static int doesNeedIncrease(Dictionary* self){
  assert(self != NULL);
  // hash table should be increased if load factor above a certain threshold
  return ((double) self->num)/((double) self->size) > 0.8;
} 

static int doesNeedDecrease(Dictionary* self){
  assert(self != NULL);
  // hash table should be decreased if load factor below a certain threshold
  // however, hash table is kept at least as large as initial size
  return (self->size > DICT_C_INITIAL_SIZE) && ((double) self->num)/((double) self->size) < 0.2;
} 


static int hash(int key, int size){
  assert(size > 0);
  int temp = key % size;
  assert((0 <= temp) && (temp < size));
  return temp;
}

static void Dictionary_increase(Dictionary* self){
  assert(self != NULL);
  assert(self->isMemEnabled);   // illegal call otherwise
  if(doesNeedIncrease(self)){   // nothing happens otherwise
    self->isMemEnabled = 0;     // no more calls to mem functions until restored
    Link** data = (Link**) malloc(self->size*2*sizeof(Link*));  // doubling
    assert(data != NULL);
    Dictionary_log("Allocating double-sized data array %lx\n", data);
    Pair* temp = Dictionary_tempVector(self); //hash table data saved in temp
    assert(temp != NULL);
    // deallocating old vector
    int i;
    for(i = 0; i < self->size; ++i){
      if(self->data[i] != NULL){
        Link_delete(self->data[i]);
      }
    }
    Dictionary_log("Deallocating data array %lx\n", self->data);
    free(self->data);
    // setting up new data
    self->size = 2*self->size;
    for(i = 0; i < self->size; ++i){
      data[i] = NULL;
    }
    self->data = data;
    int old_num = self->num;
    self->num = 0;              // will be restored after insertions
    for(i = 0; i < old_num; ++i){
      Dictionary_insert(self, temp[i].key, temp[i].value);
    }
    Dictionary_log("Deallocating temporary vector %lx\n", temp);
    free(temp);
    self->isMemEnabled = 1;     // restoring flag for further increase or decrease
  }
} 

static void Dictionary_decrease(Dictionary* self){
  assert(self != NULL);
  assert(self->isMemEnabled);   // illegal call otherwise
  if(doesNeedDecrease(self)){   // nothing happens otherwise
    self->isMemEnabled = 0;     // no more calls to mem functions until restored
    Link** data = (Link**) malloc((self->size>>1)*sizeof(Link*));  // halving
    assert(data != NULL);
    Dictionary_log("Allocating half-sized data array %lx\n", data);
    Pair* temp = Dictionary_tempVector(self); //hash table data saved in temp
    assert(temp != NULL);
    // deallocating old vector
    int i;
    for(i = 0; i < self->size; ++i){
      if(self->data[i] != NULL){
        Link_delete(self->data[i]);
      }
    }
    Dictionary_log("Deallocating data array %lx\n", self->data);
    free(self->data);
    // setting up new data
    self->size = (self->size>>1); // bitwise right shift by one positition
    for(i = 0; i < self->size; ++i){
      data[i] = NULL;
    }
    self->data = data;
    int old_num = self->num;
    self->num = 0;              // will be restored after insertions
    for(i = 0; i < old_num; ++i){
      Dictionary_insert(self, temp[i].key, temp[i].value);
    }
    Dictionary_log("Deallocating temporary vector %lx\n", temp);
    free(temp);
    self->isMemEnabled = 1;     // restoring flag for further increase or decrease
  }
}

void Dictionary_insert(Dictionary* self, int key, const void* value){
  assert(self != NULL);
  assert(self->data != NULL);
  int h = hash(key, self->size);  // hash table index corresponding to key
  if(self->data[h] == NULL){      // no existing table entry for h
    self->data[h] = Link_new();   // allocating Link-ed list to entry h
  }
  Link* list = self->data[h];          
  assert(list != NULL);
  const void* result;
  int found = Link_find(list, key, &result);
  if(!found){                     // key not currently in dictionary
    self->num++;                  // hence one more element in dictionary
  }
  Link_insert(list, key, value);  // actual insertion within list at index h
  if(self->isMemEnabled){
    Dictionary_increase(self);    // will increase size if needed
  }
}

void Dictionary_remove(Dictionary* self, int key){
  assert(self != NULL);
  assert(self->data != NULL);
  int h = hash(key, self->size);  // hash table index corresponding to key
  Link* list = self->data[h];     // Link-ed list at index h
  if(list != NULL){               // nothing to do otherwise
    const void* result;
    int found = Link_find(list, key, &result);
    if(found){                    // key is currently in dictionary
      self->num--;                // hence one less element in dictionary
      Link_remove(list, key);     // actual removal from list at index h
      if(Link_isEmpty(list)){     // dont keep empty Link-ed list, deallocate
        Link_delete(list);
        self->data[h] = NULL;
      }
    }
  }
  if(self->isMemEnabled){
    Dictionary_decrease(self);    // will decrease size if needed
  }
}

int Dictionary_find(Dictionary* self, int key, const void** result){
  assert(self != NULL);
  assert(self->data != NULL);
  int h = hash(key, self->size);  // hash table index corresponding to key
  Link* list = self->data[h];     // Link-ed list at index h
  if(list == NULL){               // Link-ed list not defined, key not in dict
    return 0;
  } else {
    return Link_find(list, key, result);
  }
}

int Dictionary_isConsistent(Dictionary* self){
  assert(self != NULL);

  if(self->data = NULL)       return 0;
  if(!self->isMemEnabled)     return 0; // flag should be restored to true 
  if(doesNeedIncrease(self))  return 0;
  if(doesNeedDecrease(self))  return 0;
  // counting table entries
  int count = 0;
  int i;
  for(i = 0; i < self->size; ++i){
    if(self->data[i] != NULL){
      LinkIter* iter = LinkIter_new(self->data[i]);
      while(LinkIter_hasNext(iter)){
        LinkIter_moveNext(iter);
        ++count;
      }
      LinkIter_delete(iter);
    }
  }
  if(count != self-> num)     return 0;
  return 1; // all tests were succesful
} 

int Dictionary_isEmpty(Dictionary* self){
  assert(self != NULL);
  return (self->num == 0) ? 1 : 0;
}




