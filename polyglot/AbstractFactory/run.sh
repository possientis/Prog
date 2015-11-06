#!/bin/sh

echo '\nThis is Java ...'
javac AbstractFactory.java; java AbstractFactory; rm *.class

echo '\nThis is C# ...'
mcs abstractFactory.cs; mono abstractFactory.exe; rm abstractFactory.exe;

echo '\nThis is C++ ...'
g++ -std=c++14 abstractFactory.cpp; ./a.out; rm a.out;
