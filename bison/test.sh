#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/bison
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

echo "Testing word parser ..."
flex word_lexer.l; bison -d word_parser.y; 
gcc word_parser.tab.c lex.yy.c -ll; ./a.out < input1.txt; ./clean.sh
echo

echo "Testing calculator ..."
flex calculator4.l; bison -d calculator4.y; 
gcc calculator4.tab.c table.c lex.yy.c -ll; ./a.out < input6.txt; ./clean.sh
echo

echo "Testing decimal number lexical analyser ..."
flex decimal.l; bison -d decimal.y; 
gcc decimal.tab.c lex.yy.c -ll; ./a.out < input3.txt; ./clean.sh
echo




cd ${DIR}
echo '\nAll flex & bison tests completed successfully\n'




