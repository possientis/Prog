#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/clone
cd ${HOME}

make
gcc test.c -lsecp256k1 -L.libs
LD_LIBRARY_PATH=.libs ./a.out


cd ${DIR}
echo '\ntest completed successfully\n'




