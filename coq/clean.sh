#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/coq
cd ${HOME}

rm -f .*.aux
rm -f *.glob
rm -f *.vo

rm -f lib/.*.aux
rm -f lib/*.glob
rm -f lib/*.vo

./set/clean.sh
./set2/clean.sh
./zf/clean.sh
./sf/clean.sh
./cat/clean.sh
./hott/clean.sh
./systemF/clean.sh
./lam/clean.sh
./cpdt/clean.sh
./grin/clean.sh
./logic/clean.sh
./ref/clean.sh
./cttwc/clean.sh

cd ${DIR}
