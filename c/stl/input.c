#include <vector>
#include <iterator>
#include <iostream>

using namespace std;

int main(){

  // Fill a vector with values read from standard input
/*
  vector<int> v;

  for(istream_iterator<int> i = cin; i != istream_iterator<int>(); ++i)
    v.push_back(*i);
*/
  // Fill a vector with values from stdin  using std::copy()
  vector<int> w;
  copy(istream_iterator<int>(cin),
      istream_iterator<int>(),
      back_inserter(w));

  copy(w.begin(),w.end(),ostream_iterator<int>(cout,"\n"));

  return 0;

}
