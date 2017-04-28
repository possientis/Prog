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
flex calculator.l; bison -d calculator.y; 
gcc calculator.tab.c lex.yy.c -ll; echo -n 123+27 | ./a.out; ./clean.sh
echo

#echo "Testing decimal number lexical analyser ..."
#flex decimal.l; gcc decimal.c lex.yy.c -ll; ./a.out < input3.txt; ./clean.sh
#echo




cd ${DIR}
echo '\nAll flex & bison tests completed successfully\n'




