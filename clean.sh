#!/bin/sh

rm -f test.log

./agda/clean.sh
./assembly/clean.sh
./bison/clean.sh
./c/clean.sh
./c++/clean.sh
./c#/clean.sh
./clojure/clean.sh
./coq/clean.sh
./gradle/clean.sh
./haskell/clean.sh
./hol/clean.sh
./java/clean.sh
./make/clean.sh
./python/clean.sh
./scala/clean.sh
./scheme/clean.sh
./tex/clean.sh

git status


