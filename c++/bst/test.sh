#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c++/bst
cd ${HOME}

make
./bst
make clean

cd ${DIR}
echo '\ntest completed succesfully\n'




