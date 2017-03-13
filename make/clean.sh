#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/make
cd ${HOME}

./guile/clean.sh
./jupiter/clean.sh
./mars/clean.sh
./saturn/clean.sh
./test/clean.sh

cd ${DIR}
