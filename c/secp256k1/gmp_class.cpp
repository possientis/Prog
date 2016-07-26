#include <iostream>
#include <gmpxx.h>
#include <string>




int main(){

  mpz_class a, b, c;

  a = 12348989898;

  b = "-6785265862816596578196578916578916589165816589";

  c = a + b;

  std::cout << "a = " << a << std::endl;
  std::cout << "b = " << b << std::endl;
  std::cout << "sum is " << c << std::endl;
  std::cout << "absolute value is " << abs(c) << std::endl;


  mpz_t p;
  mpz_init(p);
  mpz_set(p, c.get_mpz_t());

  std::cout << "p = " << p << std::endl;

  mpz_gcd(a.get_mpz_t(), b.get_mpz_t(), c.get_mpz_t());
  std::cout << "b /\\ c = " << a << std::endl;


  mpz_class x(p); // copy
  std::cout << "x = " << x << std::endl;


  mpz_class d;
  d = 726578365765786573657367856327865783267865327867832_mpz;  // cool syntax !!!!


  std::string str = d.get_str(16);
  std::cout << "d = " << str << std::endl;




  mpz_clear(p);

  return 0;
}
