#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/cs
cd ${HOME}

mv pushtest.s pushtest.ss

rm -f a.out
rm -f *.o
rm -f *.s

mv pushtest.ss pushtest.s

cd ${DIR}
