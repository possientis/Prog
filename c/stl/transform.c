#include <iostream>
#include <algorithm>
#include <ctype.h>
//#include <functional>

using namespace std;

struct to_lower {
  char operator()(char c)
  {
    return isupper(c) ? tolower(c) : c;
  }
};

char toLower(char c){ return isupper(c) ? tolower(c) : c; }

string lower(const string & str) {

  string lc;

  // toLower or to_lower()
  transform(str.begin(),str.end(),back_inserter(lc),toLower);

  return lc;

}


int main()
{

  string s = "HELLO";
  cout << s << endl;
  s = lower(s);
  cout << s << endl;

  return 0;

}
