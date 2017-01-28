#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/coq
cd ${HOME}

rm -f .*.aux
rm -f *.glob
rm -f *.vo

rm -f Lib/.*.aux
rm -f Lib/*.glob
rm -f Lib/*.vo

cd ${DIR}
