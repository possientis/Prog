#!/bin/sh

echo '\nThis is C ...'
gcc prototype.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 prototype.cpp; ./a.out; rm a.out

echo '\nThis is C# ...'
mcs prototype.cs; mono prototype.exe; rm prototype.exe

echo '\nThis is Java ...'
javac Prototype.java; java Prototype; rm *.class

echo '\nThis is JavaScript ...'
js prototype.js

echo '\nThis is Python ...'
python3 prototype.py

echo '\nThis is Scheme ...'
scm prototype.scm

echo '\nThis is Clojure ...'
clojure prototype.clj

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Prototype.scala
scala Prototype; rm *.class

echo '\nThis is Haskell ...'
ghc -v0 prototype.hs; ./prototype; rm prototype prototype.o prototype.hi
