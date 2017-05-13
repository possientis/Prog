#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/gcov
cd ${HOME}

rm -f a.out
rm -f *.o
rm -f *.gcno
rm -f *.gcda
rm -f *.gcov


cd ${DIR}
