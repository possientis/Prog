#define X abc


#if X == 0 
  printf("X = 0\n");  // will come here if X undefined, or X is some code !!
#elif X == 1
  printf("X = 1\n");
#elif X == 2
  printf("X = 2\n");
#else
  printf("X not in {0,1,2}\n");
#endif
