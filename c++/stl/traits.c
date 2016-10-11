#include <iostream>
#include <vector>
#include <string>

using namespace std;

template<typename C>
void print(const C &container)
{
  // C::iterator i = .. does not compile, need C::const_iterator i = ...
  for(typename C::const_iterator i = container.begin(); i != container.end(); ++i){

    typename C::value_type t = *i;

    cout << t << endl;

  }
}

int main()
{

  vector<string> v = {"abc","def","hij","klm"};

  print(v); // as simple as that
  //print<vector<string>>(v);   // no need, type inference for templated functions

  return 0;




}
