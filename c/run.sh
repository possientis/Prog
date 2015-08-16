#!/bin/sh

#g++  test.c  -std=c++14
#./a.out

g++ cons-prod.c -c -std=c++14
g++ cons-prod.o -pthread

./a.out
