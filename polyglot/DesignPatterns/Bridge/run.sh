#!/bin/sh
echo '\nThis is C ...'
gcc bridge.c
START=$(date +%s%N)
./a.out
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out

echo '\nThis is C++ ...'
g++ -std=c++14 bridge.cpp
START=$(date +%s%N)
./a.out
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out

echo '\nThis is Java ...'
javac Bridge.java
START=$(date +%s%N)
java Bridge
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is C# ...'
mcs bridge.cs
START=$(date +%s%N)
mono bridge.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm bridge.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Bridge.scala
START=$(date +%s%N)
scala Bridge
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is JavaScript ...'
START=$(date +%s%N)
node bridge.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is PHP ...'
START=$(date +%s%N)
php bridge.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Python ...'
START=$(date +%s%N)
python3 bridge.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby bridge.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm bridge.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Clojure ...'
clojurec bridge 1> /dev/null
START=$(date +%s%N)
java -cp .:/usr/share/java/clojure-1.6.0.jar bridge
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is Haskell ...'
ghc -v0 bridge.hs
START=$(date +%s%N)
./bridge
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm bridge bridge.o bridge.hi

