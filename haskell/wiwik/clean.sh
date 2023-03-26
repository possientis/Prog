#!/bin/sh

DIR=/home/john/Prog/haskell/wiwik
cd ${DIR}

rm -f *.hi
rm -f *.o
rm -f a.out
rm -f a.out.prof
rm -f *_stub.h
rm -f *.s
rm -f hello.dump-*
rm -f hello
rm -f *.dyn_*

./happy/clean.sh

