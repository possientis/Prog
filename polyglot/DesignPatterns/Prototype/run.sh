#!/bin/sh

echo '\nThis is C ...'
gcc prototype.c
START=$(date +%s%N)
./a.out
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 prototype.cpp
START=$(date +%s%N)
./a.out
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out

echo '\nThis is Java ...'
javac Prototype.java
START=$(date +%s%N)
java Prototype
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is C# ...'
mcs prototype.cs
START=$(date +%s%N)
mono prototype.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm prototype.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Prototype.scala
START=$(date +%s%N)
scala Prototype
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is JavaScript ...'
START=$(date +%s%N)
node prototype.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is PHP ...'
START=$(date +%s%N)
php prototype.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Python ...'
START=$(date +%s%N)
python3 prototype.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby prototype.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm prototype.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Clojure ...'
clojurec prototype 1> /dev/null
START=$(date +%s%N)
java -cp .:/usr/share/java/clojure-1.6.0.jar prototype
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is Haskell ...'
ghc -v0 prototype.hs
START=$(date +%s%N)
./prototype
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm prototype prototype.o prototype.hi
