#include <iterator>
#include <iostream>

using namespace std;

int main(){

  // Copy a file to cout via a loop
  // does not compile
  ifstream ifile("log");
  int tmp;
  while(ifile >> tmp) cout << tmp << endl;

  return 0;

}
