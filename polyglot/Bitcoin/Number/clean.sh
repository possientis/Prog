#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/polyglot/Bitcoin/Number
cd ${HOME}

./c/clean.sh
./c#/clean.sh
./java/clean.sh
./haskell/clean.sh
./scheme/clean.sh
./python/clean.sh

cd ${DIR}
