#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c++/dict
cd ${HOME}

make
./dict
make clean

cd ${DIR}
echo '\ntest completed succesfully\n'




