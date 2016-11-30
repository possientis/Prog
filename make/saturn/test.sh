#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make/saturn
cd ${HOME}

./autogen.sh
./configure
make
./src/saturn
make clean
./clean.sh



cd ${DIR}
echo '\ntest completed succesfully\n'




