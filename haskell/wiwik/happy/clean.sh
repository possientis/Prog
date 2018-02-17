#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/haskell/wiwik/happy
cd ${HOME}

rm -f *.hi
rm -f *.o

rm -f Lexer.hs
rm -f Parser.hs
rm -f a.out

cd ${DIR}
