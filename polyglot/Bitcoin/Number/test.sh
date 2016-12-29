#!/bin/sh
# need to install: 
# libmono-system-numerics4.0-cil
# libghc-hashable-dev
# libghc-crypto-random-api-dev
# libghc-monadcryptorandom-dev

set -e
DIR=`pwd`
HOME=/home/john/Prog/polyglot/Bitcoin/Number
cd ${HOME}

./java/test.sh
./c#/test.sh
./haskell/test.sh
./python/test.sh

cd ${DIR}
echo '\nAll Number tests completed successfully\n'


