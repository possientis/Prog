#!/bin/sh

DIR=/home/john/Prog/coq
cd ${DIR}

rm -f .*.aux
rm -f *.glob
rm -f *.vo

rm -f lib/.*.aux
rm -f lib/*.glob
rm -f lib/*.vo

./Logic/clean.sh
./set2/clean.sh
./zf/clean.sh
./sf/clean.sh
./cat/clean.sh
./hott/clean.sh
./systemF/clean.sh
./lam/clean.sh
./cpdt/clean.sh
./grin/clean.sh
./ref/clean.sh
./cttwc/clean.sh

