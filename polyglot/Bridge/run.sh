#!/bin/sh

echo '\nThis is Java ...'
javac Bridge.java; java Bridge; rm *.class;

echo '\nThis is JavaScript ...'
js bridge.js

echo '\nThis is C# ...'
mcs bridge.cs; mono bridge.exe; rm bridge.exe

echo '\nThis is C++ ...'
g++ -std=c++14 bridge.cpp; ./a.out; rm a.out

echo '\nThis is Python ...'
python3 bridge.py

echo '\nThis is Scheme ...'
scm bridge.scm
