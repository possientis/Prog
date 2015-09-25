#include <string.h>
#include <iostream>
#include <vector>
#include <iterator>
#include <algorithm>


using namespace std;

int main(){

  vector<const char*> v;

  v.push_back("one");
  v.push_back("two");
  v.push_back("three");
  v.push_back("four");

  cout << "Sequence cointains: ";
  copy(v.begin(),v.end(),ostream_iterator<const char*>(cout, " "));
  cout << endl;

  cout << "Searching for three.\n";

  vector<const char*>:: iterator it = find_if(v.begin(), v.end(),
      not1(bind2nd(ptr_fun(strcmp),"three")));

  if(it != v.end()){

    cout << "Found it! Here is the  rest of the story: ";
    copy(it,v.end(),ostream_iterator<const char*>(cout," "));
    cout << endl;
  }

  return 0;

}
