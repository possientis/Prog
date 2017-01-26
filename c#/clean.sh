#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/c#
cd ${HOME}

rm -f *.exe
rm -f *.dll
./bitcoin/clean.sh

cd ${DIR}
