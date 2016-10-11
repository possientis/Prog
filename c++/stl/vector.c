#include<iostream>
#include<vector>
#include<string>

using namespace std;

int main(int argc, char *argv[])
{
  vector<string> projects;

  cout << "program name:" << argv[0] << endl;

  for(int i = 1; i < argc; ++i)
    projects.push_back(argv[i]);  // also have pop_back

  for(vector<string>::iterator j = projects.begin();
      j != projects.end(); ++j)
    cout << *j << std::endl;

  // what is this?
  for(auto &j : projects)
    cout << j << endl;

  return 0;
}
