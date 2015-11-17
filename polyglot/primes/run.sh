#!/bin/sh


echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm primes.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Haskell ...'
START=$(date +%s%N)
ghc -v0 primes.hs; ./primes; rm primes; rm primes.o; rm primes.hi
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
