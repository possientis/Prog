#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/polyglot/Bitcoin/Number
cd ${HOME}

./java/bench.sh
./c#/bench.sh
./haskell/bench.sh
./python/bench.sh


cd ${DIR}

