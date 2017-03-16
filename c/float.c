#include <stdio.h>
#include <float.h>


int main()
{

  printf("FLT_MIN = %.10e\n", FLT_MIN);
  printf("FLT_MAX = %.10e\n", FLT_MAX);

  printf("DBL_MIN = %.10e\n", DBL_MIN);
  printf("DBL_MAX = %.10e\n", DBL_MAX);

  printf("LDBL_MIN = %.10e\n", LDBL_MIN);
  printf("LDBL_MAX = %.10e\n", LDBL_MAX);

  return 0;
}
