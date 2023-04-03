#!/bin/sh

set -e
DIR=/home/john/Prog/poly/Pascal
cd ${DIR}

echo '\nThis is Haskell ...'
ghc -v0 pascal.hs 
START=$(date +%s%N)
./pascal
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm pascal.hi
rm pascal.o
rm pascal


echo '\nThis is Scheme ...'
START=$(date +%s%N)
./pascal.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Python ...'
START=$(date +%s%N)
./pascal.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Java ...'
javac Pascal.java
START=$(date +%s%N)
java Pascal
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm Pascal.class


echo '\nThis is C# ...'
mcs pascal.cs
START=$(date +%s%N)
mono pascal.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm pascal.exe

echo '\nThis is C++ ...'
g++ -std=c++14 -o pascal pascal.cpp
START=$(date +%s%N)
./pascal
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm pascal
