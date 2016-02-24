#!/bin/sh
echo '\nThis is C ...'
gcc bridge.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 bridge.cpp; ./a.out; rm a.out

echo '\nThis is Java ...'
javac Bridge.java; java Bridge; rm *.class;

echo '\nThis is C# ...'
mcs bridge.cs; mono bridge.exe; rm bridge.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Bridge.scala
scala Bridge; rm *.class

echo '\nThis is JavaScript ...'
js bridge.js

echo '\nThis is PHP ...'
php bridge.php

echo '\nThis is Python ...'
python3 bridge.py

echo '\nThis is Ruby ...'
ruby bridge.rb

echo '\nThis is Scheme ...'
scm bridge.scm

echo '\nThis is Clojure ...'
clojure bridge.clj

echo '\nThis is Haskell ...'
ghc -v0 bridge.hs; ./bridge; rm bridge bridge.o bridge.hi

