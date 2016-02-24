#!/bin/sh

echo '\nThis is C ...'
gcc singleton.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 singleton.cpp; ./a.out; rm a.out

echo '\nThis is Java ...'
javac Singleton.java; java Singleton; rm *.class

echo '\nThis is C# ...'
mcs singleton.cs; mono singleton.exe; rm singleton.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Singleton.scala
scala Singleton; rm *.class

echo '\nThis is JavaScript ...'
js singleton.js

echo '\nThis is PHP ...'
php singleton.php

echo '\nThis is Python ...'
python3 singleton.py

echo '\nThis is Ruby ...'
ruby singleton.rb

echo '\nThis is Scheme ...'
scm singleton.scm

echo '\nThis is Clojure ...'
clojure singleton.clj

echo '\nThis is Haskell ...'
ghc -v0 singleton.hs; ./singleton; rm singleton singleton.o singleton.hi


