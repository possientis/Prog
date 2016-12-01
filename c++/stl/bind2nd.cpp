#include<iostream>
#include <vector>
#include<iterator>
#include <algorithm>


using namespace std;

int main(int argc, char* argv[])
{
  vector<int> v;
  v.push_back(1);
  v.push_back(4);
  v.push_back(2);
  v.push_back(8);
  v.push_back(5);
  v.push_back(7);

  // print(v)
  copy(v.begin(),v.end(), ostream_iterator<int>(cout, " "));

  int sum = count_if(v.begin(),v.end(), bind2nd(greater<int>(),5));

  cout << "\nThere are " << sum << " number(s) greater than 5\n";

//  vector<int>::iterator <- auto (type inference)
  auto nend = remove_if(v.begin(),v.end(), bind2nd(less<int>(),4));

  v.erase(nend,v.end());

  copy(v.begin(),v.end(), ostream_iterator<int>(cout, " "));

  cout << "\nElements less than 4 removed\n";

  return 0;
}
