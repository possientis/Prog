// table.h
#ifndef TABLE_INCLUDED
#define TABLE_INCLUDED

struct name{
  char* string;
  name* next;
  double value;
};

name* look(const char* p, int ins = 0);
inline name* insert(const char* s){return look(s,1);}

#endif
