#include <iostream>
#include <algorithm>
#include <iterator>

using namespace std;

struct is_odd{ // could also be a C-style function.

  bool operator ()(int i){ return (i % 2) == 1; }

};

static bool isOdd(int i){ return (i % 2) == 1; }

int main()
{

  int myints[] = {1,2,3,4,5,6,7,8,9};

  int size = sizeof myints / sizeof *myints;

  int *pbegin = myints, *pend = myints + size;

  pend = remove_if(pbegin, pend, isOdd); // or is_odd()
  cout << "range contains:";
  copy(pbegin, pend, ostream_iterator<int>(cout, " "));
  cout << endl;
  if (is_odd()(3) == true)
    cout << "by the way 3 is odd\n";

  return 0;

}
