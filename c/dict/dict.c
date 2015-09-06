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
static int hash(const K& key, int size){

  assert(size > 0);
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

  K key1 = *(K*) k1;
  K key2 = *(K*) k2;

  if(key1 == key2) return 0;

  return 1;
}


struct Dictionary_i {

  // data
  Link** table;             // array of pointers to Link lists
  int num;                  // number of entries
  int size;                 // number of available entries in hash table
  bool isMemoryEnabled;     // allowing control when resizing hash table
  // helper methods
  void init();              // called from Dictionary<K> constructor
  void destroy();           // called from Dictionary<K> destructor
  bool doesNeedIncrease();  // decides whether to allocate more space
  bool doesNeedDecrease();  // decides whether to release memory
  const void* *keyBuffer;   // needed as temporary storage when resizing
  const void* *valBuffer;   // needed as temporary storage when resizing
  void setUpBuffers();      // allocates buffers and save dictionary data
  void freeBuffers();       // free buffers (needed once resizing complete)
  void increase();          // recreating hash table from scratch with more space
  void decrease();          // recreating hash table from scratch with less space

};


template <class K>
Dictionary<K>::Dictionary(){

  d_this = new(Dictionary_i);     // allocating structure for dict private data
  assert(d_this != nullptr);
  d_this->init();                 // actual work factored out
}


void Dictionary_i::init(){
  num = 0;                        // number of elements in dictionary
  size = 4;                       // number of possible elements in hash table
  isMemoryEnabled = true;         // resizing of hash table is allowed

  table = (Link**) malloc(4*sizeof(Link*));
  assert(table != nullptr);

  for(int i = 0; i < 4; ++i){
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

  Link* temp;

  int h = hash(key,d_this->size);
  assert((0 <= h) && (h < d_this->size));   // do not take this for granted !


  if(d_this->table[h] == nullptr){  // no existing entry for this hash value
    temp = new Link(equal<K>);      // allocating new linked list
    assert(temp != nullptr);
    d_this->table[h] = temp;
  }

  temp = d_this->table[h];          // pointer to list corresponding to h
  assert(temp != nullptr);


  if(temp->find(&key) == nullptr){ // key not already present, need to increment
    d_this->num += 1;              // one more element in dictionary
  }

  temp->insert(&key,value);       // insert key into list (new value on duplicate)

}


template <class K>
const void* Dictionary<K>::find(const K& key) const {

  int h = hash(key, d_this->size);
  assert((0 <= h) && (h < d_this->size));   // do not take this for granted !

  Link* temp = d_this->table[h];            // pointer to list associated with h

  if(temp == nullptr) return nullptr;       // no entries corresponding to h

  return d_this->table[h]->find(&key);      // returning value pointer from list

}


template <class K>
void Dictionary<K>::debug(PrintKeyFunc printKey, PrintValFunc printValue) const{

  printf("----------------------------------\n");
  printf("Hash table debug:\n");
  printf("Allocated vector size: %d\n",d_this->size);
  printf("Number of elements: %d\n\n", d_this->num);
  printf("Hash table entries as follows:\n");

  for(int i = 0; i < d_this->size; ++i){

    printf("entry %d: ",i);
    if(d_this->table[i] == nullptr){
      printf("null");
    }
    else{
      LinkIter it(*(d_this->table[i])); // instantiating list iterator
      for(;it; ++it){
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


bool Dictionary_i::doesNeedIncrease(){
  return (((double) num)/((double) size) > 0.5);
}


bool Dictionary_i::doesNeedDecrease(){
  return ((((double) num)/((double) size) < 0.25) && (size >= 8));
}

void Dictionary_i::setUpBuffers(){

  keyBuffer = (const void**) malloc(num * sizeof(const void*));
  assert(keyBuffer != nullptr);

  valBuffer = (const void**) malloc(num * sizeof(const void*));
  assert(valBuffer != nullptr);

  int index = 0;  // location in newly allocated buffer

  for(int i = 0; i < size; ++i){
    if(table[i] != nullptr){  // entry exists for hash value 'i'
      for(LinkIter it(*(table[i])); it; ++it){  // looping through list
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

template <class K>
bool Dictionary<K>::isCheckOk() const{

  if (d_this == nullptr) return false;
  if (!d_this->isMemoryEnabled) return false;
  if (d_this->doesNeedIncrease()) return false;
  if (d_this->doesNeedDecrease()) return false;

  int count = 0;  // counting table entries
  for(int i = 0; i < d_this->size; ++i){
    if(d_this->table[i] != nullptr){    // hash value i hs entries
      LinkIter it(*(d_this->table[i])); // instantiating iterators over list
      for(;it;++it){
        count++;
      }
    }
  }
  if(count != d_this->num) return false;

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
