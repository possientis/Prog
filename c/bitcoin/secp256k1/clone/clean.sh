#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/clone
cd ${HOME}

rm -f  configure
rm -rf build-aux
rm -rf autom4te.cache
rm -f  aclocal.m4
rm -f ltmain.sh

rm -f *.o

cd ${DIR}


