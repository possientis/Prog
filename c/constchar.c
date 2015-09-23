#include <vector>
#include <algorithm>
#include <assert.h>
#include <string>

using namespace std;

int main(int argc,char* argv[])
{
  const char* data1[] = {"abc","def","ghf"};
  const char* const *data2 = data1;
  const char* s = "hello";

  data1[0] = s; // this is ok
  //data2[0] = s; // this will not compile


  return 0;

}
