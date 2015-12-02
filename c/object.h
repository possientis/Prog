#ifndef INCLUDED_OBJECT
#define INCLUDED_OBJECT
// encapsulating data and function pointer
struct op {
  void* (*func)(struct op* self, void* args);
  void* args;
};

void* op_run(struct op* self);
void op_init(struct op* self, void* (*func)(struct op*, void*), void* args);
struct op* op_alloc(int size);
void op_free(struct op* self);


#endif
