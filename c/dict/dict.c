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

struct Dictionary_i {

  Link** table;           // array of pointers to Link lists
  int num;                // number of entries
  int size;               // number of available entries in hash table
  bool isMemoryEnabled;   // allowing control when resizing hash table

};



template <class K>
Dictionary<K>::Dictionary(){

  d_this = new(Dictionary_i);     // allocating structure for dict private data
  assert(d_this != nullptr);

  d_this->num = 0;                // number of elements in dictionary
  d_this->size = 4;               // number of possible elements in hash table
  d_this->isMemoryEnabled = true; // resizing of hash table is allowed
  d_this->table = (Link**) malloc(4*sizeof(Link*));
  assert(d_this->table != nullptr);
  for(int i = 0; i < 4; ++i){

    d_this->table[i] = nullptr;   // no current entry for given hash value

  }

}

template<class K>
Dictionary<K>::~Dictionary(){

  // looping through hash table entry, freeing corresponding linked list
  for(int i = 0; i < d_this->size; ++i){

    if(d_this->table[i] != nullptr){

      delete d_this->table[i];  // deleting Link object associated with hash i
      d_this->table[i] = nullptr;

    }
  }

  free(d_this->table);          // freeing array of pointers to Link
  d_this->table = nullptr;

  delete(d_this);               // deleting head structure of dictionary
  d_this = nullptr;

}


template <class K>
static size_t prehash(const K& key){

  std::hash<K> hash;

  return hash(key);

}

template <class K>
static int hash(const K& key, int size){

  return (int) prehash(key) % size;

}

template <class K>
void Dictionary<K>::insert(const K& key, const void* value){

  int h = hash(key,d_this->size);

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

