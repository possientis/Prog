#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin
cd ${HOME}

./secp256k1/test.sh

cd ${DIR}
echo '\nbitcoin tests completed successfully\n'




