#!/bin/sh

set -e
DIR=/home/john/Prog/poly/Bitcoin/Number
cd ${DIR}

./java/bench.sh
./c#/bench.sh
./haskell/bench.sh
./scheme/bench.sh
./python/bench.sh
