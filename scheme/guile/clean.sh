#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/scheme/guile
cd ${HOME}

rm -f *.go
rm -f a.out
rm -f *.o
rm -f libguile-bessel.so

cd ${DIR}
