#include <queue>
#include <string>
#include <iostream>

using namespace std;

struct Place {

  size_t dist_;
  string dest_;

  Place(string dt, size_t ds): dist_(ds), dest_(dt){}

//  this works too
//  bool operator<(const Place &right) const {return (dist_ < right.dist_); }
};


bool operator<(const Place &left, const Place &right){

  return (left.dist_ < right.dist_);

}


ostream &operator<<(ostream &os, const Place &p)
{
  return os << '(' << p.dest_ << " " << p.dist_ << ')';
}

int main()
{

  priority_queue<Place> q;

  q.push(Place("Poway",10));
  q.push(Place("El Cajon",20));
  q.push(Place("La Jolla",3));

  for(; !q.empty(); q.pop())
  {
    cout << q.top() << endl;
  }

  return 0;

}
