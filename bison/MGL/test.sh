#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/bison/MGL
cd ${HOME}
echo

echo "Testing menu generator language 1 ..."
flex MGL1.l; bison -d MGL1.y;
gcc MGL1.tab.c lex.yy.c -ll; ./a.out < MGL1.txt; ./clean.sh
echo

echo "Testing menu generator language 2 ..."
flex MGL2.l; bison -d MGL2.y;
gcc MGL2.tab.c lex.yy.c -ll; ./a.out < MGL2.txt; ./clean.sh
echo

echo "Testing menu generator language 3 ..."
flex MGL3.l; bison -d MGL3.y;
gcc MGL3.tab.c lex.yy.c -ll; ./a.out < MGL3.txt; ./clean.sh
echo

echo "Testing menu generator language 4 ..."
flex MGL4.l; bison -d MGL4.y;
gcc MGL4.tab.c lex.yy.c -ll; ./a.out < MGL4.txt; ./clean.sh
echo

echo "Testing menu generator language 5 ..."
flex MGL5.l; bison -d MGL5.y;
gcc MGL5.tab.c lex.yy.c -ll; ./a.out < MGL5.txt; ./clean.sh
echo

cd ${DIR}




