#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/lean
cd ${HOME}

./hhg/clean.sh
./while/clean.sh
./tutorials/clean.sh
rm -f *.olean

cd ${DIR}
