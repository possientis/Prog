#!/bin/sh

echo '\nThis is Java ...'
javac Builder.java; java Builder; rm *.class

echo '\nThis is C# ...'
mcs builder.cs; mono builder.exe; rm builder.exe

echo '\nThis is C++ ...'
g++ -std=c++14 builder.cpp; ./a.out; rm a.out

echo '\nThis is Python ...'
python3 builder.py
