#!/bin/sh

NUM_PRIMES=138

echo '\nThis is C++ ...'
g++ -std=c++14 primes.cpp; 
START=$(date +%s%N)
./a.out $NUM_PRIMES; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out



echo '\nThis is Java ...'
javac Primes.java
START=$(date +%s%N)
java Primes $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is C# ...'
mcs primes.cs
START=$(date +%s%N)
mono primes.exe $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm primes.exe


echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Primes.scala
START=$(date +%s%N)
scala Primes $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is JavaScript ...'
START=$(date +%s%N)
js primes.js $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is PHP ...'
START=$(date +%s%N)
php primes.php $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm primes.scm $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Haskell ...'
ghc -v0 primes.hs;
START=$(date +%s%N)
./primes $NUM_PRIMES 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm primes; rm primes.o; rm primes.hi


