#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make/mars
cd ${HOME}

./autogen.sh
./configure
make
./src/mars
make clean
./clean.sh



cd ${DIR}
echo '\ntest completed succesfully\n'




