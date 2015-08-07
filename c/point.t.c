// point.t.c
#include "point.h"
#include <stdlib.h> // qsort()
#include <iostream>

using namespace std;

static int pointCompare(const void *addrPoint1Ptr,
                        const void *addrPoint2Ptr)
{
  const Point &p1 = ** (const Point **) addrPoint1Ptr;
  const Point &p2 = ** (const Point **) addrPoint2Ptr;
  double d1sq = p1.x() * (double) p1.x() + p1.y() * (double) p1.y();
  double d2sq = p2.x() * (double) p2.x() + p2.y() * (double) p2.y();
  return d1sq < d2sq ? -1 : 1;
}

static ostream& operator<<(ostream& o, const Point& p)
{
  return o << '(' << p.x() << ',' << p.y() << ')';
}

static ostream& print(ostream& o, const Point *const *array, int size)
{
  o << '{';
  for(int i = 0; i < size; ++i){
    o << ' ' << *array[i];
  }

  return o << " }";
}


const int SIZE =6;

static Point a(0,15), b(2,12), c(4,9), d(6,6), e(8,3), f(10,0);

static Point *array[SIZE] = { &a, &b, &c, &d, &e, &f };

main()
{
  print(cout, array, SIZE) << endl;
  cout << "Now sort by distance from origin:" << endl;
  qsort(array, SIZE, sizeof *array, pointCompare);
  print (cout, array, SIZE) << endl;
}
