#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1
cd ${HOME}

echo "testing library C preprocessor macros"
gcc test_macro.c; ./a.out; rm -f a.out

cd ${DIR}
echo '\nsecp256k1 tests completed successfully\n'




