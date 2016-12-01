#include <iostream>
#include <vector>
#include<set>
#include <algorithm>
#include <assert.h>
#include <string>

using namespace std;

int main(int argc,char* argv[])
{
  int a[] = {1,2,3,4,6,5,7,8};
  int size = (sizeof(a)/sizeof(*a));
  assert(size == 8);

  int *ibegin = a;
  int *iend = a + size;
  const int *iter = adjacent_find(ibegin,iend,greater<int>());

  if(iter != iend)
  {
    cout << "Element " << iter - a << " is out of order: "
         << *iter << " > " << *(iter + 1) << "." << endl;
  }


  //
  return 0;

}
