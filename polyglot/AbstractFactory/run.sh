#!/bin/sh

echo '\nThis is C ...'
gcc abstractFactory.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 abstractFactory.cpp; ./a.out; rm a.out;

echo '\nThis is C# ...'
mcs abstractFactory.cs; mono abstractFactory.exe; rm abstractFactory.exe;

echo '\nThis is Java ...'
javac AbstractFactory.java; java AbstractFactory; rm *.class

echo '\nThis is JavaScript ...'
js abstractFactory.js

echo '\nThis is Python ...'
python3 abstractFactory.py

echo '\nThis is Scheme ...'
scm abstractFactory.scm

echo '\nThis is Clojure ...'
clojure abstractFactory.clj

echo '\nThis is Haskell ...'
ghc -v0 abstractFactory.hs; ./abstractFactory;
rm abstractFactory abstractFactory.hi abstractFactory.o

