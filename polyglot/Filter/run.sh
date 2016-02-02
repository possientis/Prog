#!/bin/sh

echo '\nThis is C ...'
gcc filter.c; ./a.out 2>/dev/null; rm a.out   # diverting stderr (debug info)

echo '\nThis is C++ ...'
g++ -std=c++14 filter.cpp; ./a.out; rm a.out

echo '\nThis is C# ...'
mcs filter.cs; mono filter.exe; rm filter.exe

echo '\nThis is Java ...'
javac Filter.java; java Filter; rm *.class

echo '\nThis is JavaScript ...'
js filter.js

echo '\nThis is PHP ...'
php filter.php

echo '\nThis is Python ...'
python3 filter.py

echo '\nThis is Ruby ...'
ruby filter.rb

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Filter.scala
scala Filter; rm *.class

echo '\nThis is Haskell ...'
ghc -v0 -XMultiParamTypeClasses -XTypeSynonymInstances -XFlexibleInstances \
  filter.hs; ./filter; rm filter filter.o filter.hi



