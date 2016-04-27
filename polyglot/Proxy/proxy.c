// Proxy Design Pattern
#include <stdio.h>

// This code exercise is borrowed from Design Patterns in C# - 13 Proxy 
// https://www.youtube.com/watch?v=XvbDqLrnkmA

// A proxy is a class which functions as an interface to something else

// There are three participants to the proxy design pattern:
//
// 1. subject
// 2. real subject
// 3. proxy
//

// The subject is the common interface between the real object and proxy
// the real object is that which the proxy is meant to be substituted for

typedef struct ComponentPrice_VirtualTable_ ComponentPrice_VirtualTable;
typedef struct ComponentPrice_              ComponentPrice;

struct ComponentPrice_VirtualTable_ {
  double (*cpu_price)(ComponentPrice* self);
  double (*ram_price)(ComponentPrice* self);
  double (*ssd_price)(ComponentPrice* self);
};




int main(){

  return 0;
}


