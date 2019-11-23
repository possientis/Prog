#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/tex/cats
cd ${HOME}

rm -f *.aux
rm -f *.idx
rm -f *.log
rm -f *.out
rm -f *.toc

cd ${DIR}
