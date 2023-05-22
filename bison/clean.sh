#!/bin/sh

DIR=${HOME}/Prog/bison
cd ${DIR}

rm -f *.tab.c
rm -f *.tab.h
rm -f lex.yy.c
rm -f *.o
rm -f a.out

./calc/clean.sh
./MGL/clean.sh
