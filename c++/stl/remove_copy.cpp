#include <iostream>
#include <vector>
#include <iterator>
#include <algorithm>


using namespace std;

int main(int argc, char* argv[])
{
  vector<int> v1,v2,v3;
  v1.push_back(1);
  v1.push_back(2);
  v1.push_back(3);
  v1.push_back(4);

  remove_copy_if(v1.begin(),v1.end(),back_inserter(v2),
      bind2nd(greater<int>(),3));

  copy(v2.begin(),v2.end(),ostream_iterator<int>(cout, " "));
  cout << endl;


  remove_copy_if(v1.begin(),v1.end(),back_inserter(v3),
      not1(bind2nd(greater<int>(),3)));

  copy(v3.begin(),v3.end(),ostream_iterator<int>(cout, " "));
  cout << endl;

  return 0;
}
