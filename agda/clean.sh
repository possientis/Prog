#!/bin/sh

DIR=/home/john/Prog/agda
cd ${DIR}

rm -f *.agdai
rm -f *.agda~
rm -f *.agda#
rm -f hello-world
rm -rf MAlonzo

./vfpa/clean.sh
./plfa/clean.sh
./aop/clean.sh
