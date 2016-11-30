#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make/jupiter
cd ${HOME}

./autogen.sh
./configure
make
./src/jupiter
make clean
./clean.sh



cd ${DIR}
echo '\ntest completed succesfully\n'




