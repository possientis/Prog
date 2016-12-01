#include <map>
#include <iostream>
#include <string>
#include <algorithm>

typedef std::map<std::string,int> My_Map;

struct print {

  void operator () (const My_Map::value_type &p)
  {
    std::cout << p.second << " " << p.first << std::endl;
  }
};

void print_it (const My_Map::value_type &p)
{
  std::cout << p.second << " " << p.first << std::endl;

}

int main(){

  using namespace std;

  My_Map my_map;

  // word couting
  for(string a_word; cin >> a_word; ) my_map[a_word]++;


  // print() build an object of type print
  for_each (my_map.begin(), my_map.end(),print());

  // same as
  //print myprint;
  //for_each (my_map.begin(), my_map.end(),myprint);
  //
  //same as
  //for_each (my_map.begin(), my_map.end(),print_it); // passing ptr to func
  //

  return 0;
}


