#include <iostream>
#include <string>
#include <algorithm>


using namespace std;

int main(){

  string s = "spaces in the text";
  cout << s << endl;

  // remove_if just returns a 'new end' iterator, without deleting anything
  string::iterator nend = remove_if(s.begin(),s.end(),
      bind2nd(equal_to<char>(),' '));

  // need to call erase method, using 'new end' iterator
  s.erase(nend,s.end());

  cout << s << endl;



  return 0;

}

