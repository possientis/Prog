#include <iostream>
#include <algorithm>
#include <iterator>

using namespace std;

int main()
{

  int myints[] = {10, 20, 30, 30, 20, 10, 10, 20};

  int size = sizeof myints / sizeof *myints;

  int *pbegin = myints, *pend = myints + size;

  cout << "original array contains:";
  copy(pbegin, pend, ostream_iterator<int>(cout," "));

  int *nend = remove(pbegin, pend, 20);
  cout << "\nrange contains:";
  copy(pbegin, nend, ostream_iterator<int>(cout, " "));

  cout << "\ncomplete array contains:";
  copy(pbegin, pend, ostream_iterator<int>(cout, " "));
  cout << endl;

  return 0;

}
