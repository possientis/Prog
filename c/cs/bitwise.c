#include "bitwise.h"

int least_byte(int x) { return x & 0xff; }

int complement_all_but_least(int x) {
    return (~x & 0xffffff00) | least_byte(x);
}

int least_set_to_one(int x) {
    return (x & 0xffffff00) | 0xff;
}


int bis(int x, int m) { return x | m; }
int bic(int x, int m) { return ~(~x | m); }

int bool_or(int x, int y) { return bis(x,y); }
int bool_xor(int x, int y) { return bool_or(bic(x,y), bic(y,x)); } 
