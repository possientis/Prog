// STL queue
#include <iostream>
#include <queue>
#include <string>


using namespace std;

int main()

{
  queue<string> q;
  cout << "Pushing one two three\n";

  q.push("one");
  q.push("two");
  q.push("three");

  for(; !q.empty(); q.pop()){

    cout << "\nPopping: ";
    cout << q.front();

  }

  cout << endl;



  return 0;

}
