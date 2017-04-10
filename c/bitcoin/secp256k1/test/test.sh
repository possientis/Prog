#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/test
cd ${HOME}

echo
echo "secp256k1 tests starting..."

echo
echo "testing secp256k1 library C preprocessor macros..."
gcc test_macro.c; ./a.out; rm -f a.out

echo
echo "testing secp256k1 library..." 
gcc main.c test.c -lsecp256k1; ./a.out; rm -f a.out

cd ${DIR}
echo
echo '\nsecp256k1 tests completed successfully\n'




