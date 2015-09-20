#include <deque>
#include <iostream>
#include <iterator>
#include<algorithm>

int main(){

  using namespace std;

  deque<int> a_deck;

  a_deck.push_back(3);
  a_deck.push_front(1);
  a_deck.insert(a_deck.begin() + 1,2);
  a_deck[2]=0;
  copy(a_deck.begin(), a_deck.end(), ostream_iterator<int>(cout, " "));

  cout << endl;

  int array1[] = {1,2,0};
  int array2[] = {10,20};

  copy(array1,array1+3,array2);

  cout << array2[0] << " " << array2[1] << endl;

  return 0;
}


