#include <iostream>
#include <algorithm>

using namespace std;

template <typename T>
struct print {
  print(ostream &out): os_(out), count_(0){}
  void operator() (const T &t) { os_ << t << ' '; ++count_; }
  ostream &os_;
  int count_;
};

template <typename T>
void simplePrint(const T &t){ cout << t << ' ';}

int main()
{

  int A[] = {1, 4, 2, 8, 5, 7};
  const int N = sizeof A /sizeof *A;

  // for_each() returns function object after being applied to each element
  print<int> f = for_each(A, A + N, print<int>(cout));
  cout << endl << f.count_ << " objects printed." << endl;

  for_each(A, A + N, simplePrint<int>);
  cout << endl;

  return 0;

}
