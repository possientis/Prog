#!/bin/sh

DIR=/home/john/Prog/make/jupiter
cd ${DIR}

rm -f autom4te.cache -r
rm -f config.*
rm -f configure
rm -f install-sh
rm -f Makefile
rm -f src/Makefile
rm -f src/jupiter
rm -f src/a.out   # just in case
# tree -a
