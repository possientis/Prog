// C99 standard
#include<complex.h>
#include<stdio.h>

int main()
{

  float complex a;
  float _Complex b; // 'complex' is macro defined as '_Complex' in complex.h
  complex float c;

  double complex d;
  complex double e;

  long complex double f;

  printf("size of float complex = %d\n", sizeof(float complex));
  printf("size of double complex = %d\n", sizeof(double complex));
  printf("size of long double complex = %d\n", sizeof(long double complex));

  printf("size of I = %d\n", sizeof(I));  // double complex

  complex double z = 3.0 + 4.0*I;
  printf("Re(z) = %f\n", creal(z));
  printf("Im(z) = %f\n", cimag(z));
  printf("|z| = %f\n", cabs(z));
  printf("arg(z) = %f\n", carg(z));
  printf("arg(i) = %f\n", carg(I));

  __complex__ float gnu1;         // gnu extension
  __complex__ double gnu2;        // gnu extension
  __complex__ long double gnu3;   // gnu extension
  __complex__ int gnu4;           // etc etc, works for all primitives types

  printf("size of __complex__ float= %d\n", sizeof(__complex__ float));
  printf("size of __complex__ double = %d\n", sizeof(__complex__ double));
  printf("size of __complex__ long double = %d\n", sizeof(__complex__ long double));

  __complex__ double zz = 4 + 3i;  // this works !!!

  double x = __real__ zz;
  double y = __imag__ zz;

  printf("Re(zz) = %f\n", x);
  printf("Im(zz) = %f\n", y);

  printf("|zz| = %f\n", cabs(zz));  // this works !!!

  return 0;
}
