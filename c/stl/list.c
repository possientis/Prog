#include <list>
#include <iostream>
#include <iterator>
#include <string>
#include<algorithm>

int main(){

  using namespace std;

  list<string> a_list;
  a_list.push_back("banana");
  a_list.push_front("apple");
  a_list.push_back("carrot");

  ostream_iterator<string> out_it(cout,"\n");

  copy(a_list.begin(),a_list.end(),out_it);
  cout << endl;
  reverse_copy(a_list.begin(),a_list.end(),out_it);
  cout << endl;
  copy(a_list.rbegin(),a_list.rend(),out_it);

  return 0;
}


