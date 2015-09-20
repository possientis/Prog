#include<iostream>
#include<vector>
#include<string>

using namespace std;

int main(int argc, char *argv[])
{
  vector<string> projects;

  cout << "program name:" << argv[0] << endl;

  for(int i = 1; i < argc; ++i){
    projects.push_back(argv[i]);  // also have pop_back
    cout << projects[i-1] << endl;
  }

  return 0;
}
