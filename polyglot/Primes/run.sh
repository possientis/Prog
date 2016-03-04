#!/bin/sh

NUM_PRIMES=256

echo '\nThis is C# ...'
mcs primes.cs
START=$(date +%s%N)
mono primes.exe $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm primes.exe

echo '\nThis is C# ...'
mcs oldprimes.cs
START=$(date +%s%N)
mono oldprimes.exe $NUM_PRIMES
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm oldprimes.exe


echo '\nThis is Scheme ...'
START=$(date +%s%N)
./primes.scm $NUM_PRIMES
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


