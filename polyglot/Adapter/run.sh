#!/bin/sh

echo '\nThis is C ...'
gcc adapter.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 adapter.cpp; ./a.out; rm a.out

echo '\nThis is C# ...'
mcs adapter.cs; mono adapter.exe; rm adapter.exe

echo '\nThis is Java ...'
javac Adapter.java; java Adapter; rm *.class

echo '\nThis is JavaScript ...'
js adapter.js

echo '\nThis is PHP ...'
php adapter.php

echo '\nThis is Python ...'
python3 adapter.py

echo '\nThis is Ruby ...'
ruby adapter.rb

echo '\nThis is Scheme ...'
scm adapter.scm

echo '\nThis is Clojure ...'
clojure adapter.clj

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Adapter.scala
scala Adapter; rm *.class

echo '\nThis is Haskell ...'
ghc -v0 adapter.hs; ./adapter; rm adapter adapter.o adapter.hi

