#!/bin/sh

echo '\nThis is Scheme ...'
scm primes.scm

echo '\nThis is Haskell ...'
ghc -v0 primes.hs; ./primes; rm primes; rm primes.o; rm primes.hi
