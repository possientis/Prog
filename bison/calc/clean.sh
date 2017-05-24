#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/bison/calc
cd ${HOME}

rm -f *.tab.c
rm -f *.tab.h
rm -f lex.yy.c
rm -f *.o
rm -f a.out

cd ${DIR}

