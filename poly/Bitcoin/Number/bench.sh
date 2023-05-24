#!/bin/sh

set -e
DIR=${HOME}/Prog/poly/Bitcoin/Number
cd ${DIR}

./java/bench.sh
./c#/bench.sh
./haskell/bench.sh
./scheme/bench.sh
./python/bench.sh
