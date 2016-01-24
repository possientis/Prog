#!/bin/sh

echo '\nThis is C ...'
gcc filter.c; ./a.out 2>/dev/null; rm a.out   # diverting stderr (debug info)

echo '\nThis is C++ ...'
g++ -std=c++14 filter.cpp; ./a.out; rm a.out

echo '\nThis is Java ...'
javac Filter.java; java Filter; rm *.class
