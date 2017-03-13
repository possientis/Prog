#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/make/guile
cd ${HOME}

rm -f .cache -r
rm -f autom4te.cache -r
rm -f aclocal.m4
rm -f config.*
rm -f configure
rm -f Makefile
rm -f simple-guile
rm -f *.o
rm -f hello.scm

#tree -a

cd ${DIR}
