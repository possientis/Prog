#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/haskell/wiwik
cd ${HOME}

rm -f *.hi
rm -f *.o
rm -f a.out
rm -f *_stub.h
rm -f *.s

cd ${DIR}
