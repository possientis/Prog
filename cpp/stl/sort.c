#include <iostream>
#include <vector>
#include <algorithm>
#include <iterator>


using namespace std;

// who needs 'functors'
static bool lessThan(string s1, string s2)
{
  return (s1 < s2);
}

int main()
{
  vector<string>  v = {"def","hij","klm","abc"};

  copy(v.begin(), v.end(), ostream_iterator<string>(cout, " "));
  cout << endl;

  sort(v.begin(), v.end(), less<string>()); // or greater<string>() or lessThan

  copy(v.begin(), v.end(), ostream_iterator<string>(cout, " "));
  cout << endl;


  return 0;

}
