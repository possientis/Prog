#!/bin/sh

echo '\nThis is Java ...'
javac Prototype.java; java Prototype; rm *.class

echo '\nThis is C# ...'
mcs prototype.cs; mono prototype.exe; rm prototype.exe

echo '\nThis is C++ ...'
g++ -std=c++14 prototype.cpp; ./a.out; rm a.out

echo '\nThis is Python ...'
python3 prototype.py

echo '\nThis is Scheme ...'
scm prototype.scm
