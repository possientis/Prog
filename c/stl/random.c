#include <vector>
#include <iterator>
#include <iostream>
#include <assert.h>
#include <algorithm>

using namespace std;

int main(){

  vector<int> v(1,1); // [1]
  v.push_back(2);
  v.push_back(3);
  v.push_back(4); // [1,2,3,4]

  vector<int>::iterator i = v.begin();
  vector<int>::iterator j = i + 2; cout << *j << " ";
  i += 3; cout << *i << " ";
  j = i - 1; cout << *j << " ";
  j -= 2; cout << *j << " ";
  cout << v[1] << endl;

  (j < i) ? cout << "j < i" : cout << "not (j < i)";
  cout << endl;

  (j > i) ? cout << "j > i" : cout << "not (j > i)";
  cout << endl;

  i = j;
  i <= j && j <= i ? cout << "i & j equal" : cout << "i & j not equal";
  cout << endl;
  return 0;

}
