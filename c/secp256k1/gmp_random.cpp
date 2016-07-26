// g++ [-std=c++14] filename.cpp -lgmp -lgmpxx
#include <iostream>
#include <time.h>
#include <gmpxx.h>

int main(){

  gmp_randclass r (gmp_randinit_default); // other init algo exist

  time_t current = time(NULL);
  std::cout << "current time is : " << current << std::endl;

  r.seed(current);  // best to seed with /dev/urandom though

  mpz_class q = r.get_z_bits(256);

  std::cout << std::hex << "random q = " << q << std::endl;

  r.seed(q);       // seeding with 256 bit random seed


  std::cout << std::hex << "random q = " << r.get_z_bits(256) << std::endl;
  std::cout << std::hex << "random q = " << r.get_z_bits(256) << std::endl;
  std::cout << std::hex << "random q = " << r.get_z_bits(256) << std::endl;
  std::cout << std::hex << "random q = " << r.get_z_bits(256) << std::endl;
  std::cout << std::hex << "random q = " << r.get_z_bits(256) << std::endl;
  std::cout << std::hex << "random q = " << r.get_z_bits(256) << std::endl;






  return 0;
}
