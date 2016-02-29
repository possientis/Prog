#!/bin/sh


echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm primes.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Haskell ...'
ghc -v0 primes.hs;
START=$(date +%s%N)
./primes 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm primes; rm primes.o; rm primes.hi

echo '\nThis is C# ...'
mcs primes.cs
START=$(date +%s%N)
mono primes.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm primes.exe


