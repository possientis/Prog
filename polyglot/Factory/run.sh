#!/bin/sh
echo '\nThis is C ...'
gcc factory.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 factory.cpp; ./a.out; rm a.out

echo '\nThis is C# ...'
mcs factory.cs; mono factory.exe; rm factory.exe

echo '\nThis is Java ...'
javac Factory.java; java Factory; rm *.class

echo '\nThis is JavaScript ...'
js factory.js

echo '\nThis is Python ...'
python3 factory.py

echo '\nThis is Scheme ...'
scm factory

echo '\nThis is Clojure ...'
clojure factory.clj

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Factory.scala
scala Factory; rm *.class

echo '\nThis is Haskell ...'
ghc -v0 factory.hs; ./factory; rm factory factory.o factory.hi



