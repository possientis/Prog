#!/bin/sh

#g++  test.c  -std=c++14
#./a.out

g++ tickets.c -c -std=c++14
g++ tickets.o -pthread

./a.out
