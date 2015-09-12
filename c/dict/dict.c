// dict.c
#include "dict.h"
#include "assert.h"   // assert()
#include "malloc.h"   // malloc(), free()
#include <stdio.h>    // printf()

#include <functional> // std::hash<T>

#ifndef INCLUDED_LINK
#include "link.h"
#endif

// just to make code below more readable
typedef void (*PrintKeyFunc)(const void*);
typedef void (*PrintValFunc)(const void*);


// prehash function used based on std::hash<T>
template <class K>
static size_t prehash(const K& key){

  std::hash<K> hash;
  return hash(key);

}


// hash function used which uses hash table size as argument
// Simple prehash modulo size: can be improved at a later stage
template <class K>
static int hash(const void* keyp, int size){

  assert(size > 0);

  const K& key = *((K*) keyp);

  int temp = (int) (prehash(key) % size);// bad especially as size is power of 2
  if(temp < 0) temp += size;        // do not assume output of % operator is > 0
  assert((0 <= temp) && (temp < size));

  return temp;
}

// generic (const void*)-like equality operator allowing comparisons
// between elements of type K. Needed to instantiate generic linked
// list of type Link.
template <class K>
static int equal(const void* k1, const void* k2){

  const K& key1 = *((K*) k1);
  const K& key2 = *((K*) k2);

  return (key1 == key2) ? 0 : 1;

}


struct Dictionary_i {

  // data
  Link** table;                   // array of pointers to Link lists
  int num;                        // number of entries
  int size;                       // number of available entries in hash table
  const void* *keyBuffer;         // needed as temporary storage when resizing
  const void* *valBuffer;         // needed as temporary storage when resizing
  int(*hash)(const void* key, int size);// some hash<K>, depending on K
  int (*equal)(const void* key1,const void* key2);// some equal<K>
  bool isMemoryEnabled;           // allowing control when resizing hash table
  // helper methods
  void init();                    // called from Dictionary<K> constructor
  void destroy();                 // called from Dictionary<K> destructor
  bool doesNeedIncrease() const;  // decides whether to allocate more space
  bool doesNeedDecrease() const;  // decides whether to release memory
  bool isCheckOk() const;         // performs some sanity checks
  void setUpBuffers();            // allocates buffers and save dictionary data
  void freeBuffers();             // free buffers (not needed once resizing complete)
  const void* find( const void* key) const;
  void insert(const void* key, const void* value);
  void del(const void* key);      // delete key from dictionary
  void increase();                // recreating hash table with more space
  void decrease();                // recreating hash table with less space
  void debug(PrintKeyFunc,PrintValFunc) const;
};


template <class K>
Dictionary<K>::Dictionary(){

  d_this = new(Dictionary_i);     // allocating structure for dict private data
  assert(d_this != nullptr);
  d_this->init();                 // actual work factored out
  d_this->hash = hash<K>;         // cannot be done inside 'init'
  d_this->equal = equal<K>;       // cannot be done inside 'init'
}


void Dictionary_i::init(){
  const int INIT_SIZE = 4;
  num = 0;                        // number of elements in dictionary
  size = INIT_SIZE;                       // number of possible elements in hash table
  isMemoryEnabled = true;         // resizing of hash table is allowed

  table = (Link**) malloc(INIT_SIZE*sizeof(Link*));
  assert(table != nullptr);

  for(int i = 0; i < INIT_SIZE; ++i){
    table[i] = nullptr;           // no current entry for given hash value
  }

  keyBuffer = nullptr;            // no buffer allocated on start up
  valBuffer = nullptr;            // no buffer allocated on start up
}


template<class K>
Dictionary<K>::~Dictionary(){

  d_this->destroy();            // actual work factored out
  delete(d_this);               // deleting head structure of dictionary
  d_this = nullptr;             // prevents re-use
}


void Dictionary_i::destroy(){

  // looping through hash table entry, freeing corresponding linked list
  for(int i = 0; i < size; ++i){
    if(table[i] != nullptr){
      delete table[i];          // deleting Link object associated with hash i
      table[i] = nullptr;       // prevents re-use
    }
  }

  free(table);                  // freeing array of pointers to Link
  table = nullptr;              // revents re-use
}


template <class K>
void Dictionary<K>::insert(const K& key, const void* value){

  d_this->insert(&key,value);

}


void Dictionary_i::insert(const void* key, const void* value)
{

  int h = hash(key,size);
  assert((0 <= h) && (h < size)); // do not take this for granted !

  if(table[h] == nullptr){        // no existing entry for this hash value
    Link* temp = new Link(equal); // allocating new linked list
    assert(temp != nullptr);
    table[h] = temp;
  }

  Link* temp = table[h];                // pointer to list corresponding to h
  assert(temp != nullptr);


  if(temp->find(key) == nullptr){// key not already present, need to increment
    num += 1;                    // one more element in dictionary
  }

  temp->insert(key,value);       // insert key into list (new value on duplicate)

  if(isMemoryEnabled) increase();// will resize hash table if load factor too high

}


template <class K>
void Dictionary<K>::del(const K& key){

  d_this->del(&key);

}


void Dictionary_i::del(const void* key){

  int h = hash(key,size);         // Dictionary_i::hash
  assert((0 <= h) && (h < size)); // do not take this for granted !

  Link* temp = table[h];          // pointer to list corresponding to h

  if(temp != nullptr){            // nothing to do otherwise, nothing to delete

    if(temp->find(key) != nullptr){

      num -= 1;                   // key exists, one less element after deletion
    }

    temp->del(key);               // delete key from linked list

    if(temp->isEmpty()){          // link list corresponding to h is now empty
      delete table[h];
      table[h] = nullptr;         // needed to ensure correctness of insert
    }

    if(isMemoryEnabled) decrease();// resize hash table if load factor too low
  }

}


template <class K>
const void* Dictionary<K>::find(const K& key) const {

  return d_this->find(&key);

}


const void* Dictionary_i::find(const void* key) const{

  int h = hash(key, size);
  assert((0 <= h) && (h < size));           // do not take this for granted !

  Link* temp = table[h];                    // pointer to list associated with h

  if(temp == nullptr) return nullptr;       // no entries corresponding to h

  return table[h]->find(key);               // returning value pointer from list

}


template <class K>
void Dictionary<K>::debug(PrintKeyFunc printKey, PrintValFunc printValue) const{

  d_this->debug(printKey,printValue);
}


void Dictionary_i::debug(PrintKeyFunc printKey, PrintValFunc printValue) const{

  printf("----------------------------------\n");
  printf("Hash table debug:\n");
  printf("Allocated vector size: %d\n",size);
  printf("Number of elements: %d\n\n", num);
  printf("Hash table entries as follows:\n");

  for(int i = 0; i < size; ++i){

    printf("entry %d: ",i);
    if(table[i] == nullptr){
      printf("null");
    }
    else{
      for(LinkIter it(*table[i]);it; ++it){
          printf("key = ");
          printKey(it.key());
          printf(": value = ");
          printValue(it.val());
          printf(",  ");
      }
    }
    printf("\n");
  }
  printf("----------------------------------\n");
}


bool Dictionary_i::doesNeedIncrease() const {
  return (((double) num)/((double) size) > 0.8);
}


bool Dictionary_i::doesNeedDecrease() const{
  return ((((double) num)/((double) size) < 0.2) && (size >= 8));
}

void Dictionary_i::setUpBuffers(){

  keyBuffer = (const void**) malloc(num * sizeof(const void*));
  assert(keyBuffer != nullptr);

  valBuffer = (const void**) malloc(num * sizeof(const void*));
  assert(valBuffer != nullptr);

  int index = 0;  // location in newly allocated buffer

  for(int i = 0; i < size; ++i){
    if(table[i] != nullptr){  // entry exists for hash value 'i'
      for(LinkIter it(*table[i]); it; ++it){  // looping through list
        assert((0 <= index) && (index < num));
        keyBuffer[index] = it.key();
        valBuffer[index] = it.val();
        index += 1;
      }
    }
  }

  assert(index == num);
}

void Dictionary_i::freeBuffers(){

  free(keyBuffer);
  free(valBuffer);

}

void Dictionary_i::increase(){

  assert(isMemoryEnabled);  // should not be called unless isMemoryEnabled true

  if(doesNeedIncrease()){   // nothing happens otherwise

    isMemoryEnabled = false;// no more resizing until this is complete
    setUpBuffers();         // saving table entries in temporary buffer
    destroy();              // de-allocating existing hash table
    size *= 2;              // doubling size of table
    table = (Link**) malloc(size*sizeof(Link*)); // re-allocation
    assert(table != nullptr);
    for(int i = 0; i < size; ++i){
      table[i] = nullptr;   // no current entry for given hash value
    }
    int count = num;        // remember total number of elements saved in buffers
    num = 0;                // no more elements in table

    for(int i = 0; i < count; ++i){
      insert(keyBuffer[i],valBuffer[i]);  // re-inserting elements from buffers
    }

    freeBuffers();          // de-allocating temporary buffers (key and value)
    isMemoryEnabled = true; // resizing now permitted (but probably not needed)

  }
}


void Dictionary_i::decrease(){

  assert(isMemoryEnabled);  // should not be called unless isMemoryEnabled true

  if(doesNeedDecrease()){   // nothing happens otherwise

    isMemoryEnabled = false;// no more resizing until this is complete
    setUpBuffers();         // saving table entries in temporary buffer
    destroy();              // de-allocating existing hash table
    size /= 2;              // halving size of table
    table = (Link**) malloc(size*sizeof(Link*)); // re-allocation
    assert(table != nullptr);
    for(int i = 0; i < size; ++i){
      table[i] = nullptr;   // no current entry for given hash value
    }
    int count = num;        // remember total number of elements saved in buffers
    num = 0;                // no more elements in table

    for(int i = 0; i < count; ++i){
      insert(keyBuffer[i],valBuffer[i]);  // re-inserting elements from buffers
    }

    freeBuffers();          // de-allocating temporary buffers (key and value)
    isMemoryEnabled = true; // resizing now permitted (but probably not needed)

  }
}


template <class K>
bool Dictionary<K>::isCheckOk() const{

  if (d_this == nullptr) return false;

  return d_this->isCheckOk();

}


bool Dictionary_i::isCheckOk() const{

  if (!isMemoryEnabled) return false;
  if (doesNeedIncrease()) return false;
  if (doesNeedDecrease()) return false;

  int count = 0;                        // counting table entries
  for(int i = 0; i < size; ++i){
    if(table[i] != nullptr){            // hash value i has entries
      for(LinkIter it(*table[i]);it;++it){
        count++;
      }
    }
  }
  if(count != num) return false;        // 'num' does not match actual number

  return true;
}



// the following lines are to enforce compilation of code
// for the given cases of class K. This allows keeping this
// implementation file separate from the header file dict.h
// If you need to use Dictionary<K> for a different class
// K, please add the corresponding line and recompile.
// see https://stackoverflow.com/questions/495021/why-can-templates-only-be-implemented-in-the-header-file
#include <string>     // std::string
template class Dictionary<int>;
template class Dictionary<std::string>;
