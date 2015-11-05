#include <set>
#include <iostream>
#include <iterator>
#include <assert.h>

int main(){

  using namespace std;

  //multiset<int> myset // allows duplicate keys
  set<int> myset;

  for(int i =1; i <=5; ++i) myset.insert(i*10);

  pair<set<int>::iterator,bool> ret = myset.insert(20);
  // check that insertion failed, as 20 already part of set
  assert(ret.second == false);

  int myints[] = {5, 10, 15};
  myset.insert(myints,myints+3);

  // also works in c++11
  myset.insert({60,70,80});   // new 'initializer range' syntax

  copy(myset.begin(),myset.end(),ostream_iterator<int>(cout,"\n"));


  return 0;
}


