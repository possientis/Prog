#!/bin/sh
# need to install: 
# libmono-system-numerics4.0-cil
# libghc-hashable-dev
# libghc-crypto-random-api-dev
# libghc-monadcryptorandom-dev

set -e
DIR=${HOME}/Prog/poly/Bitcoin/Number
cd ${DIR}

./java/test.sh
./c#/test.sh
./haskell/test.sh
./scheme/test.sh
./python/test.sh

echo '\nAll Number tests completed successfully\n'
