#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/test
cd ${HOME}

echo
echo "secp256k1 tests starting..."

cp Makefile.bak Makefile
make; LD_LIBRARY_PATH=../clone/.libs ./a.out; ./clean.sh

cd ${DIR}
echo
echo '\nsecp256k1 test completed successfully\n'




