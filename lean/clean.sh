#!/bin/sh

DIR=${HOME}/Prog/lean
cd ${DIR}

./hhg/clean.sh
./while/clean.sh
./tutorials/clean.sh
rm -f *.olean
