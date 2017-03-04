#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/make
cd ${HOME}

./jupiter/clean.sh
./mars/clean.sh
./saturn/clean.sh
./test/clean.sh

cd ${DIR}
