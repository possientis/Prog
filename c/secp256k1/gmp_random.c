// gcc filename.c -lgmp

#include <stdio.h>
#include <assert.h>
#include <time.h>
#include<gmp.h>



int main(){

  gmp_randstate_t state;        // generating random numbers requires a state
  gmp_randinit_default(state);  // various algorithms exists to initialize state

  mpz_t q;                      // a variable need to be declared
  mpz_init(q);                  // and initialized (heap allocation)

  // in order to have a different pseudo-random sequence for each run,
  // the state needs to be seeded. A simle solution is to rely on system time

  time_t current = time(NULL);
  assert(sizeof(current) == sizeof(long));
  gmp_randseed_ui(state, current);

  mpz_urandomb(q,state,256);
  
  // you can also use an mpz_t variable to seed
  gmp_randseed(state,q);


  // rather than system time, sourcing randomness from /dev/urandom may be better
  FILE* f = fopen("/dev/urandom","r");
  assert(f != NULL);
  unsigned char temp[32]; // lets read 256 bits
  // reading one item of 32 bytes from f into buffer temp
  assert(fread(temp,32,1,f) == 1);
  // importing 32 bytes of data into variable q
  mpz_import(q, 32/sizeof(long),1, sizeof(long), 0, 0, temp);
  printf("/dev/urandom q = "); mpz_out_str(stdout,16,q); printf("\n");
  assert(fclose(f) == 0);
  gmp_randseed(state,q);


  mpz_urandomb(q,state,256); // actual pseudo-random generation


  // direct io of variable
  printf("random q = "); mpz_out_str(stdout,16,q); printf("\n");
  // alternatively, variable can be serialized (encoded) and usual string io
  char buffer[128];             // adjust size, depending on number of digits
  mpz_get_str(buffer,16,q);
  printf("random q = %s\n", buffer);
  // even better
  gmp_printf("random q = %Zx\n", q);  // 'Zd' for decimal
  

  mpz_clear(q);                 // frees heap
  gmp_randclear(state);         // frees heap

  return 0;
}


