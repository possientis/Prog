// example from http://www.cplusplus.com/articles/y8hv0pDG/
#include <iostream>
#include <string>



void print_me_bad(std::string& s){ // should be const string &
  std::cout << s << std::endl;
}

void print_me_good(const std::string& s){
  std::cout << s << std::endl;
}

int main(){

  const std::string s1("Hello");
  std::string s2("world");

  //print_me_bad(s1);   // does not compile: cannot initialize non-const ref with const ref
  print_me_bad(s2);     // this is ok: non const ref initialize with non-const ref
  // print_me_bad(std::string("world"));  // does not compile, cannot initialize non-const ref with temporary?
  // print_me_bad("!"); // does not compile

  print_me_good(s1);
  print_me_good(s2);
  print_me_good(std::string("world"));
  print_me_good("!");

  return 0;

};
