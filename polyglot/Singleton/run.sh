#!/bin/sh

echo '\nThis is Java ...'
javac Singleton.java; java Singleton; rm *.class

echo '\nThis is C# ...'
mcs singleton.cs; mono singleton.exe; rm singleton.exe

echo '\nThis is C++ ...'
g++ -std=c++14 singleton.cpp; ./a.out; rm a.out

echo '\nThis is Python ...'
python3 singleton.py

echo '\nThis is Scheme ...'
scm singleton.scm

echo '\nThis is C ...'
gcc singleton.c; ./a.out; rm a.out
