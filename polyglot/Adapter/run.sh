#!/bin/sh

echo '\nThis is Java ...'
javac Adapter.java; java Adapter; rm *.class

echo '\nThis is C# ...'
mcs adapter.cs; mono adapter.exe; rm adapter.exe

echo '\nThis is C++ ...'
g++ -std=c++14 adapter.cpp; ./a.out; rm a.out
