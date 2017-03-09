#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/flex
cd ${HOME}
echo


echo "Testing word recognizer with symbol table ..."
flex word_with_symtable.l; gcc lex.yy.c -ll; ./a.out < input.txt; ./clean.sh

cd ${DIR}
echo '\nAll flex tests completed successfully\n'




