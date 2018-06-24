#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/cs
cd ${HOME}

./syscall/clean.sh
./rio/clean.sh
./network/clean.sh
./conc/clean.sh

mv pushtest.s pushtest.ss

rm -f a.out
rm -f *.o
rm -f *.s
rm -f gmon.out
rm -f log
rm -f *.lo
rm -fr .libs 

mv pushtest.ss pushtest.s

cd ${DIR}
