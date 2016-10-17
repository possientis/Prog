#!/bin/sh

CURRENT=`pwd`

echo '\nThis is Java ...'
cd java
./compile.sh Bench_Number.java
START=$(date +%s%N)
java Bench_Number
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class
cd $CURRENT

echo '\nThis is C# ...'
cd c#
./compile.sh Bench_Number.cs
START=$(date +%s%N)
mono Bench_Number.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.dll *.exe
cd $CURRENT


