#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c++/dc
cd ${HOME}

make
./dc
make clean

cd ${DIR}
echo '\ntest completed succesfully\n'




