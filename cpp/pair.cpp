#include "pair.h"
#include<iostream>

pair::pair(int x, int y)
{
  d_x = x;
  d_y = y;
}

int pair::x(void) const
{
  return d_x;
}

int pair::y(void) const
{
  return d_y;
}


void pair::set (int x, int y)
{
  d_x = x;
  d_y = y;
}

void pair::print(void) const
{
  std::cout << "(" << d_x << "," << d_y << ")";
}
