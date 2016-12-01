#include<iostream>
#include <vector>
#include<deque>
#include<iterator>


using namespace std;

int main(int argc, char* argv[])
{
  vector<int> v(10,1);
  deque<int> l;

  copy(v.begin(),v.end(),back_inserter(l));
  copy(l.begin(),l.end(),ostream_iterator<int>(cout," "));


  return 0;
}
