#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/bitcoin/secp256k1/clone
cd ${HOME}

rm -f  aclocal.m4
rm -rf autom4te.cache
rm -f build-aux/compile
rm -f build-aux/config.guess
rm -f build-aux/config.sub
rm -f build-aux/install-sh
rm -f build-aux/ltmain.sh
rm -f build-aux/missing
rm -f build-aux/depcomp
rm -f build-aux/test-driver
rm -f build-aux/m4/*
rm -f configure
rm -f config.status
rm -f config.log
rm -f src/libsecp256k1-config.h.in~
rm -f src/libsecp256k1-config.h.in
rm -f COPYING
rm -f INSTALL
rm -f Makefile.in
rm -f src/Makefile.in
rm -rf .libs
rm -f libsecp256k1.la
rm -f libsecp256k1.pc
rm -f libtool 
rm -f Makefile
rm -rf src/.deps
rm -f src/.dirstamp
rm -rf src/.libs
rm -f src/libsecp256k1-config.h
rm -f src/libsecp256k1_la-secp256k1.lo
rm -f src/libsecp256k1_la-secp256k1.o
rm -f src/stamp-h1

rm -f *.o

tree -a

cd ${DIR}

