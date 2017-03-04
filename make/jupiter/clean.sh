#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/make/jupiter
cd ${HOME}

rm -f autom4te.cache -r
rm -f config.*
rm -f configure
rm -f install-sh
rm -f Makefile
rm -f src/Makefile
rm -f src/jupiter
rm -f src/a.out   # just in case
# tree -a

cd ${DIR}
