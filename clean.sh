#!/bin/sh

rm -f test.log
./assembly/clean.sh
./logic/clean.sh
./c/clean.sh
./c++/clean.sh
./c#/clean.sh
./java/clean.sh
./scala/clean.sh
./clojure/clean.sh



rm -f haskell/*.hi
rm -f haskell/*.o
rm -f haskell/test
rm -f scala/*.class
rm -f coq/*.glob
rm -f coq/*.vo
rm -f coq/.*.aux
rm -f coq/Lib/*.glob
rm -f coq/Lib/*.vo
rm -f coq/Lib/.*.aux
rm -fr python/__pycache__
rm -fr python/bitcoin/Number/__pycache__
git status


