#!/bin/sh
echo '\nThis is C ...'
gcc composite.c; ./a.out; rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 composite.cpp; ./a.out; rm a.out

echo '\nThis is Java ...'
javac Composite.java; java Composite; rm *.class

echo '\nThis is C# ...'
mcs composite.cs; mono composite.exe; rm composite.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Composite.scala
scala Composite; rm *.class

echo '\nThis is JavaScript ...'
js composite.js

echo '\nThis is PHP ...'
php composite.php

echo '\nThis is Python ...'
python3 composite.py

echo '\nThis is Ruby ...'
ruby composite.rb

echo '\nThis is Haskell ...'
ghc -v0 composite.hs; ./composite; rm composite composite.hi composite.o

