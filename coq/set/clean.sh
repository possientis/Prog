#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/coq/set
cd ${HOME}

rm -f .*.aux
rm -f *.glob
rm -f *.vo

cd ${DIR}