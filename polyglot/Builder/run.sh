#!/bin/sh

echo '\nThis is C ...'
gcc builder.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 builder.cpp; ./a.out; rm a.out

echo '\nThis is C# ...'
mcs builder.cs; mono builder.exe; rm builder.exe

echo '\nThis is Java ...'
javac Builder.java; java Builder; rm *.class

echo '\nThis is JavaScript ...'
js builder.js

echo '\nThis is Python ...'
python3 builder.py

echo '\nThis is Scheme ...'
scm builder.scm

echo '\nThis is Clojure ...'
clojure builder.clj

echo '\nThis is Haskell ...'
ghc -v0 builder.hs; ./builder; rm builder builder.o builder.hi     

