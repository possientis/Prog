#!/bin/sh

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
rm -f src/a.out   # just in case
tree


# autoreconf -i 

