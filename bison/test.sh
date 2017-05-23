#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/bison
cd ${HOME}
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
echo '\nAll flex & bison tests completed successfully\n'




