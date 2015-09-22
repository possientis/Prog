#include <vector>
#include <iterator>
#include <iostream>
#include <assert.h>
#include <algorithm>

using namespace std;

int main(){

  vector<int> v(3,1);   // [1,1,1]
  v.push_back(7);       // [1,1,1,7]
  replace(v.begin(),v.end(),7,1);
  assert(find(v.begin(),v.end(),7) == v.end());

  copy(v.begin(),v.end(),ostream_iterator<int>(cout,", "));


  return 0;

}
