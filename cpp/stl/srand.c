#include <iostream>
#include <vector>
#include <algorithm>
#include <iterator>

using namespace std;

int main()
{

  // new random seed
  srand(time(0));

  vector<int> v, v2(10,20);
  generate_n(back_inserter(v), 10, rand);


  // zipWith modulo v v2
  transform(v.begin(),v.end(),v2.begin(),v.begin(), modulus<int>());
  copy(v.begin(),v.end(),ostream_iterator<int>(cout, "\n"));

  int factor = 2;

  // map (*2) v
  transform(v.begin(), v.end(), v.begin(), bind2nd(multiplies<int>(), factor));
  copy(v.begin(),v.end(),ostream_iterator<int>(cout, "\n"));

  return 0;

}
