#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/haskell/song
cd ${HOME}

rm -f *.hi
rm -f *.o
rm -f a.out

rm -f Test/*.hi
rm -f Test/*.o

cd ${DIR}
