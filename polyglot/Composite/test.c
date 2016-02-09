
typedef struct A_ A;

struct A_ {
};


void foo(A* self){
  A* copy;
  copy = A_copy(self);
}

A* A_copy(A* self){
  return self;
}

int main(){
  return 0;
}
