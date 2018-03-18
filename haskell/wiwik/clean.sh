#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/haskell/wiwik
cd ${HOME}

rm -f *.hi
rm -f *.o
rm -f a.out
rm -f a.out.prof
rm -f *_stub.h
rm -f *.s
rm -f hello.dump-*
rm -f hello

./happy/clean.sh

cd ${DIR}
