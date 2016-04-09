// dict.h
#ifndef INCLUDE_DICT_H
#define INCLUDE_DICT_H 
typedef struct Dictionary_ Dictionary; 

Dictionary* Dictionary_new();
Dictionary* Dictionary_copy(Dictionary* self);
void        Dictionary_delete(Dictionary* self);
int         Dictionary_isEmpty(Dictionary* self);
void        Dictionary_insert(Dictionary* self, int key, const void* value);
void        Dictionary_remove(Dictionary* self, int key);
            // returns 1 if found, 0 otherwise
int         Dictionary_find(Dictionary* self, int key, const void** result); 
int         Dictionary_toString(Dictionary* self, char* buf, int size);
int         Dictionary_isConsistent(Dictionary* self);
void        Dictionary_debug(Dictionary* self);
int         Dictionary_hasMemoryLeak();



#endif


