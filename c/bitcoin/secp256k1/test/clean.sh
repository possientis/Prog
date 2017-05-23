#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/test
cd ${HOME}

rm -f *.o
rm -f a.out
rm -f log{,1,2} # brace expansion requires bash

rm -f aclocal.m4
rm -rf autom4te.cache
rm -f compile
rm -f configure
rm -f install-sh
rm -f Makefile
rm -f missing
rm -f COPYING
rm -f INSTALL


cd ${DIR}

