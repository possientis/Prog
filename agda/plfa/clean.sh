#!/bin/sh

DIR=${HOME}/Prog/agda/plfa
cd ${DIR}

rm -f *.agdai
rm -f *.agda~
rm -f *.agda#

./Lam/clean.sh
./DeBruijn/clean.sh

