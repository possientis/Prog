#!/bin/sh
echo '\nThis is C ...'
gcc bridge.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 bridge.cpp; ./a.out; rm a.out

echo '\nThis is C# ...'
mcs bridge.cs; mono bridge.exe; rm bridge.exe

echo '\nThis is Java ...'
javac Bridge.java; java Bridge; rm *.class;

echo '\nThis is JavaScript ...'
js bridge.js

echo '\nThis is Python ...'
python3 bridge.py

echo '\nThis is Scheme ...'
scm bridge.scm

echo '\nThis is Clojure ...'
clojure bridge.clj

echo '\nThis is Haskell ...'
ghc -v0 bridge.hs; ./bridge; rm bridge bridge.o bridge.hi

