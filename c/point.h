// point
#ifndef INCLUDED_POINT
#define INCLUDED_POINT

class Point {
  int d_x;
  int d_y;

  public:
  Point(int x, int y) : d_x(x), d_y(y){}
  Point(const Point& p) : d_x(p.d_x), d_y(p.d_y){}
  ~Point(){}

  Point& operator=(const Point& p){
    d_x=p.d_x; d_y = p.d_y; return *this;}
  void setX(int x){d_x = x;}
  void setY(int y){d_y = y;}
  int x() const {return d_x;}
  int y() const {return d_y;}
};

#endif
