#include <iostream>
#include <iterator>
#include <algorithm>
//#include <ctype.h>
//#include <functional>

using namespace std;

int main()
{

  vector<float> v(5,1); // v = [1.0, 1.0, 1.0, 1.0, 1.0]
  copy(v.begin(), v.end(),ostream_iterator<float>(cout," "));
  cout << endl;

  partial_sum(v.begin(), v.end(), v.begin());
  copy(v.begin(), v.end(),ostream_iterator<float>(cout," "));
  cout << endl;

  transform(v.begin(),v.end(), v.begin(), v.begin(), multiplies<float>());
  copy(v.begin(), v.end(),ostream_iterator<float>(cout," "));
  cout << endl;

  transform(v.begin(), v.end(), v.begin(), bind2nd(divides<float>(),3));
  copy(v.begin(), v.end(),ostream_iterator<float>(cout," "));
  cout << endl;

  return 0;

}
