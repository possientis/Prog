#!/bin/sh

set -e 
DIR=${HOME}/Prog/bison
cd ${DIR}
echo

echo "Testing word recognizer with symbol table ..."
flex word_with_symtable.l; gcc lex.yy.c -ll; ./a.out < words.txt; ./clean.sh
echo

echo "Testing hand written lexer ..."
gcc hand_lexer.c; ./a.out < lexer.txt; ./clean.sh
echo

echo "Testing equivalent auto lexer ..."
flex auto_lexer.l; gcc lex.yy.c -ll; ./a.out < lexer.txt; ./clean.sh
echo

echo "Testing word parser ..."
flex word_lexer.l; bison -d word_parser.y; 
gcc word_parser.tab.c lex.yy.c -ll; ./a.out < words.txt; ./clean.sh
echo

echo "Testing decimal number lexical analyser ..."
flex decimal.l; bison -d decimal.y; 
gcc decimal.tab.c lex.yy.c -ll; ./a.out < decimal.txt; ./clean.sh
echo

./calc/test.sh
./MGL/test.sh

echo '\nAll flex & bison tests completed successfully\n'
