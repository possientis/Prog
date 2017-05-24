#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/bison/calc
cd ${HOME}
echo

echo "Testing calculator 1 ..."
flex calculator1.l; bison -d calculator1.y; 
gcc calculator1.tab.c lex.yy.c -ll; ./a.out < calc1.txt; ./clean.sh
echo

echo "Testing calculator 2 ..."
flex calculator2.l; bison -d calculator2.y; 
gcc calculator2.tab.c lex.yy.c -ll; ./a.out < calc2.txt; ./clean.sh
echo

echo "Testing calculator 3 ..."
flex calculator3.l; bison -d calculator3.y; 
gcc calculator3.tab.c lex.yy.c -ll; ./a.out < calc3.txt; ./clean.sh
echo

echo "Testing calculator 4 ..."
flex calculator4.l; bison -d calculator4.y; 
gcc calculator4.tab.c table.c lex.yy.c -ll; ./a.out < calc4.txt; ./clean.sh
echo

echo "Testing calculator 5 ..."
flex calculator5.l; bison -d calculator5.y; 
gcc calculator5.tab.c table.c lex.yy.c -ll -lm; ./a.out < calc5.txt; ./clean.sh
echo

echo "Testing calculator 6 ..."
flex calculator6.l; bison -d calculator6.y; 
gcc calculator6.tab.c table.c lex.yy.c -ll -lm; ./a.out < calc6.txt; ./clean.sh
echo

cd ${DIR}




