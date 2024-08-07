#!/bin/sh

DIR=${HOME}/Prog/make/saturn
cd ${DIR}

rm -f aclocal.m4
rm -f autom4te.cache -r
rm -f compile
rm -f config.*
rm -f configure
rm -f COPYING
rm -f depcomp
rm -f INSTALL
rm -f install-sh
rm -f Makefile.in
rm -f Makefile
rm -f src/Makefile.in
rm -f src/Makefile
rm -f missing
rm -f src/saturn
rm -f src/*.o
rm -f src/a.out   # just in case
rm -f stamp-h1
rm -f src/.deps -r
rm -f test-driver
rm -f src/greptest.*
rm -f src/test-suite.log
rm -f common/*.a
rm -f common/*.o
rm -f common/Makefile.in
rm -f common/Makefile
rm -f common/.deps -r
rm -f saturn-1.0 -r
rm -f *.tar.gz

# tree -a

# autoreconf -i 

