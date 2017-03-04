#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/make/mars
cd ${HOME}

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
rm -f src/mars
rm -f src/*.o
rm -f src/a.out   # just in case
rm -f stamp-h1
rm -f src/.deps -r
rm -f src/.libs -r
rm -f test-driver
rm -f src/greptest.*
rm -f src/test-suite.log
rm -f common/*.a
rm -f common/*.o
rm -f common/*.lo
rm -f common/*.la
rm -f common/Makefile.in
rm -f common/Makefile
rm -f common/.deps -r
rm -f common/.libs -r
rm -f include/Makefile.in
rm -f include/Makefile
rm -f libmar/Makefile.in
rm -f libmar/Makefile
rm -f libmar/.deps -r
rm -f libmar/.libs -r
rm -f libtool
rm -f ltmain.sh
rm -f mars-1.0 -r
rm -f *.tar.gz
rm -f libmar/libmars*

rm -f src/modules/hithere/.deps -r
rm -f src/modules/hithere/.libs -r
rm -f src/modules/hithere/*.o
rm -f src/modules/hithere/*.lo
rm -f src/modules/hithere/*.la
rm -f src/modules/hithere/Makefile
rm -f src/modules/hithere/Makefile.in

# tree -a
# autoreconf -i 

cd ${DIR}
