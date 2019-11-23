#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/tex
cd ${HOME}

./logic/clean.sh
./notes/clean.sh
./cats/clean.sh

cd ${DIR}
