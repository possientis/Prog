#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c++/avl
cd ${HOME}

make
./avl
make clean

cd ${DIR}
echo '\ntest completed succesfully\n'




