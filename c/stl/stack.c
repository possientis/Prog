// STL stack
#include <iostream>
#include <stack>


using namespace std;

int main()

{
  stack<char> st;

  st.push('A');
  st.push('B');
  st.push('C');
  st.push('D');

  for(; !st.empty(); st.pop()){

    cout << "\nPopping: ";
    cout << st.top();

  }

  cout << endl;



  return 0;

}
