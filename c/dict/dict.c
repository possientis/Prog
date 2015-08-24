// dict.c
#include "dict.h"
#include "assert.h"
#include "malloc.h"
#include <stdio.h>

#ifndef INCLUDED_LINK
#include "link.h"
#endif

// just to make code below more readable
typedef int (*Comparator)(const void*, const void*);  // == 0 on equality
typedef void (*PrintKeyFunc)(const void*);
typedef void (*PrintValFunc)(const void*);

struct Dictionary_i {

  int (*sameKey)(const void*, const void*); // == 0 when keys are equal
  Link** table;           // array of pointers to Link lists
  unsigned int num;       // number of entries
  unsigned int size;      // number of available entries in hash table
  bool isMemoryEnabled;   // allowing control when resizing hash table

};

// creating dictionary from comparison operator
Dictionary::Dictionary(Comparator comp){

  d_this = new(Dictionary_i);     // allocating structure for dict private data
  assert(d_this != nullptr);

  d_this->num = 0;                // number of elements in dictionary
  d_this->size = 4;               // number of possible elements in hash table
  d_this->sameKey = comp;         // == 0 on equality between keys
  d_this->isMemoryEnabled = true; // resizing of hash table is allowed
  d_this->table = (Link**) malloc(4*sizeof(Link*));
  assert(d_this->table != nullptr);
  for(int i = 0; i < 4; ++i){

    d_this->table[i] = nullptr;   // no current entry for given hash value

  }

}

Dictionary::~Dictionary(){

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

