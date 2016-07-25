#include <stdio.h>
#include <assert.h>
#include<gmp.h>



int main(){

  mpz_t p;
  mpz_init(p);


  const char* p_hex = 
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";

  assert(mpz_set_str(p, p_hex, 16) == 0);

  mpz_t q;
  assert(mpz_init_set_str(q, p_hex, 16) == 0);

  assert(mpz_cmp(p,q) == 0);

  char buffer[128];

  assert(mpz_get_str(buffer,10,p) == buffer);
  printf("p = %s\n", buffer);
  printf("p = "); mpz_out_str(stdout,10,p); printf("\n");



  int primality = mpz_probab_prime_p(p,50); // proba < 4^(-50) of being wrong
  
  switch(primality){
    case 2:
      printf("p is definitely prime\n"); break;
    case 1:
      printf("p is very probably prime\n"); break;
    case 0:
      printf("p is composite\n"); break;
    default:
      assert(NULL);
  }

  mpz_sub_ui(q,p,50);
  assert(mpz_get_str(buffer,10,q) == buffer);
  printf("q = %s\n", buffer);
  printf("q = "); mpz_out_str(stdout,10,q); printf("\n");

  mpz_nextprime(q,q);
  assert(mpz_get_str(buffer,10,q) == buffer);
  printf("q = %s\n", buffer);
  printf("q = "); mpz_out_str(stdout,10,q); printf("\n");

  mpz_sub_ui(q,p,50);
  mpz_gcd(q,q,p);
  assert(mpz_get_str(buffer,10,q) == buffer);
  printf("q = %s\n", buffer);
  printf("q = "); mpz_out_str(stdout,10,q); printf("\n");

  /*
  printf("please enter a number in hex:");
  assert(mpz_inp_str(q, stdin, 16) != 0);
  printf("q = "); mpz_out_str(stdout,10,q); printf("\n");

  printf("please do it again:");scanf("%s", buffer);
  assert(mpz_set_str(q,buffer,16) == 0);
  printf("q = "); mpz_out_str(stdout,10,q); printf("\n");
  */

  
  gmp_randstate_t state;
  gmp_randinit_default(state);

  mpz_urandomb(q,state,256);
  printf("random q = "); mpz_out_str(stdout,16,q); printf("\n");


  unsigned long a[20];
  mpz_import(q,32,1,sizeof(a[0]),0,0,a);
  printf("q = "); mpz_out_str(stdout,16,q); printf("\n");


  printf("size of p in base 16 is:%d\n", mpz_sizeinbase(p,2));

  

  mpz_clear(q);
  mpz_clear(p);

  return 0;
}



