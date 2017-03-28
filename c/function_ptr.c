int foo(void){ return 0; }

int main(){

  int (*fp1) (void) = foo;  // '&' not necessary for function pointers
  int (*fp2) (void) = &foo; // '&' is possible

  return 0;
}
