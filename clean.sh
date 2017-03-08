#!/bin/sh

rm -f test.log

./assembly/clean.sh
./c/clean.sh
./make/clean.sh
./c++/clean.sh
./java/clean.sh
./c#/clean.sh
./haskell/clean.sh
./scheme/clean.sh
./python/clean.sh
./scala/clean.sh
./clojure/clean.sh
./coq/clean.sh
./logic/clean.sh
./flex/clean.sh

git status


