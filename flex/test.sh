#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/flex
cd ${HOME}
echo


echo "Testing word recognizer with symbol table ..."
flex word_with_symtable.l; gcc lex.yy.c -ll; ./a.out < input1.txt; ./clean.sh
echo

echo "Testing hand written lexer ..."
gcc hand_lexer.c; ./a.out < input2.txt; ./clean.sh
echo

echo "Testing equivalent auto lexer ..."
flex auto_lexer.l; gcc lex.yy.c -ll; ./a.out < input2.txt; ./clean.sh
echo

echo "Testing decimal number lexical analyser ..."
#flex decimal.l; gcc decimal.c lex.yy.c -ll; ./a.out < input3.txt; ./clean.sh
echo


cd ${DIR}
echo '\nAll flex tests completed successfully\n'




