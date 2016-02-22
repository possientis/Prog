#!/bin/sh
echo '\nThis is C ...'
gcc composite.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 composite.cpp; ./a.out; rm a.out

echo '\nThis is C# ...'
mcs composite.cs; mono composite.exe; rm composite.exe

echo '\nThis is Java ...'
javac Composite.java; java Composite; rm *.class
