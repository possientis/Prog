#include <iostream>
#include <iterator>
#include <vector>

using namespace std;

int main()
{

  vector<int> v;

  cout << "Type in a few integers (Ctrl+D when done)\n";

  istream_iterator<int> begin = istream_iterator<int>(cin);
  istream_iterator<int> end = istream_iterator<int>();
  copy(begin,end,back_inserter(v));

  copy(v.begin(),v.end(),ostream_iterator<int>(cout," "));
  cout << endl;


  return 0;

}
