#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/agda
cd ${HOME}

rm -f *.agdai
rm -f *.agda~
rm -f *.agda#
rm -f hello-world

./vfpa/clean.sh
./plfa/clean.sh
./aop/clean.sh

cd ${DIR}
