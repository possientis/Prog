#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c/hacking
cd ${HOME}

rm -f *.o
rm -f a.out
rm -f log
rm -f log1
rm -f log2
rm -f log3
rm -f notesearch
rm -f notetaker
rm -f shellcode

./hello/clean.sh


cd ${DIR}