// dict.h
#ifndef INCLUDE_DICT_H
#define INCLUDE_DICT_H 
typedef struct Dictionary_ Dictionary; 

Dictionary* Dictionary_copy(Dictionary*);
Dictionary* Dictionary_new();
void        Dictionary_delete(Dictionary*);
int         Dictionary_isEmpty(Dictionary*);
int         Dictionary_insert(int key, void* value);
int         Dictionary_delkey(int key);
void*       Dictionary_find(int key);
int         Dictionary_toString(Dictionary*, char* buf, int size);
int         Dictionary_isConsistent(Dictionary*);
int         Dictionary_hasMemoryLeak();



#endif


