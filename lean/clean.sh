#!/bin/sh

DIR=/home/john/Prog/lean
cd ${DIR}

./hhg/clean.sh
./while/clean.sh
./tutorials/clean.sh
rm -f *.olean
