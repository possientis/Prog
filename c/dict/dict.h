// dict.h
#ifndef INCLUDE_DICT_H
#define INCLUDE_DICT_H 
typedef struct Dictionary_ Dictionary; 

Dictionary* Dictionary_new();
Dictionary* Dictionary_copy(Dictionary* self);
void        Dictionary_delete(Dictionary* self);
int         Dictionary_isEmpty(Dictionary* self);
int         Dictionary_insert(int key, void* value);
int         Dictionary_delkey(int key);
void*       Dictionary_find(int key);
int         Dictionary_toString(Dictionary* self, char* buf, int size);
int         Dictionary_isConsistent(Dictionary* self);
int         Dictionary_hasMemoryLeak();



#endif


