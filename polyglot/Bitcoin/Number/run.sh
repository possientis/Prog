#!/bin/sh

echo '\nThis is Java ...'
CURRENT=`pwd`
cd java
javac Test_Number.java
javac Bench_Number.java
START=$(date +%s%N)
java Test_Number
java Bench_Number
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class
cd $CURRENT
