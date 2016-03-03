#!/bin/sh

echo '\nThis is C ...'
gcc filter.c
START=$(date +%s%N)
./a.out 2>/dev/null
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out   

echo '\nThis is C++ ...'
g++ -std=c++14 filter.cpp
START=$(date +%s%N)
./a.out
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out

echo '\nThis is Java ...'
javac Filter.java
START=$(date +%s%N)
java Filter
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is C# ...'
mcs filter.cs
START=$(date +%s%N)
mono filter.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm filter.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Filter.scala
START=$(date +%s%N)
scala Filter
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is JavaScript ...'
START=$(date +%s%N)
js filter.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is PHP ...'
START=$(date +%s%N)
php filter.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


START=$(date +%s%N)
echo '\nThis is Python ...'
python3 filter.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby filter.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm filter.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Clojure ..'
clojurec filter 1> /dev/null
START=$(date +%s%N)
java -cp .:/usr/share/java/clojure-1.6.0.jar filter
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is Haskell ...'
ghc -v0 -XMultiParamTypeClasses -XTypeSynonymInstances -XFlexibleInstances \
  filter.hs
START=$(date +%s%N)
./filter
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm filter filter.o filter.hi



