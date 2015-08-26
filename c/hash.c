// hash example
#include<iostream>
#include<functional>
#include<string>
#include<limits>


int main()
{

  char nts1[] = "Testofthe length of hashing";
  char nts2[] = "Testofthe length of hashing";

  std::string str1(nts1);
  std::string str2(nts2);

  std::hash<char*> ptr_hash;
  std::hash<std::string> str_hash;

  std::cout << "same hashes:\n" << std::boolalpha;
  std::cout << "nts1 and nts2: " << (ptr_hash(nts1) == ptr_hash(nts2)) << '\n';
  std::cout << "str1 and str2: " << (str_hash(str1) == str_hash(str1)) << '\n';

  std::cout << "hash of nts1 is: " << std::hex << ptr_hash(nts1) << '\n';
  std::cout << "hash of nts2 is: " << std::hex << ptr_hash(nts2) << '\n';
  std::cout << "hash of str1 is: " << std::hex << str_hash(str1) << '\n';
  std::cout << "hash of str2 is: " << std::hex << str_hash(str2) << '\n';
  std::cout << "numeric limit of size_t is:" << std::hex;
  std::cout << std::numeric_limits<size_t>::max() << '\n';

  return 0;

}
