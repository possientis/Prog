#include <iostream>
#include <vector>
#include <algorithm>
#include <iterator>

using namespace std;

int main()
{
  vector<int> v(10,2);
  partial_sum(v.begin(),v.end(),v.begin());
  random_shuffle(v.begin(), v.end());

  copy(v.begin(),v.end(),ostream_iterator<int>(cout, " "));
  cout << endl;

  cout << "Numbers greater than 10 = "
       << count_if(v.begin(), v.end(), bind2nd(greater<int>(),10))
       << endl;


  return 0;

}
