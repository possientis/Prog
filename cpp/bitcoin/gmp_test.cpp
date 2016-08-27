// g++ [-std=c++14] filename.cpp -lgmp -lgmpxx
#include <iostream>
#include <gmpxx.h>



int main(){

  mpz_t p;
  mpz_init(p);

  const char* p_hex = 
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";

  // parsing
  mpz_set_str(p, p_hex, 16);

  std::cout << "p = " << p << std::endl;
  std::cout << std::hex << "p = " << p << std::endl;

  std::cout << "type in a long integer:";
  std::cin >> p;
  std::cout << std::dec << "p = " << p << std::endl;



  mpz_clear(p);



  return 0;
}
