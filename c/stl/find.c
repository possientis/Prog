#include <iostream>
#include <vector>
#include<set>
#include <algorithm>
#include <assert.h>
#include <string>

using namespace std;

int main(int argc,char* argv[])
{
  // on vector<string>
  const char* data[] = {"abc","def","ghf"};

  vector<string> v;

  for(int i = 1; i < 3; ++i) v.push_back(string(data[i]));

  vector<string>::iterator j = find(v.begin(),v.end(),string("def"));

  if (j == v.end()) return 1;

  assert( (*j) == string("def"));

  // on built-in array
  int a[] = {10,30,20,15};
  int size = (sizeof(a)/sizeof(*a));
  assert(size == 4);

  int *ibegin = a;
  int *iend = a + size;
  int *iter = find(ibegin,iend,20);

  if(iter == iend)
    cout << "20 was not found\n";
  else
    cout << "20 was found\n";

  // on set
  set<int> int_set(a,a+size);
  set<int>::iterator it1 = int_set.find(20);  // set method, faster
  set<int>::iterator it2 = find(int_set.begin(),int_set.end(),20);

  if(it1 == int_set.end())
    cout << "set find method failed to find 20\n";
  else
    cout << "set find method succeeded in finding 20\n";

  if(it2 == int_set.end())
    cout << "generic find method failed to find 20\n";
  else
    cout << "generic find method succeeded in finding 20\n";

  //
  return 0;

}
