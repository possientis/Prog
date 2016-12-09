#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make/mars
cd ${HOME}

./autogen.sh
./configure
make
./src/mars
make check
make clean
./clean.sh



cd ${DIR}
echo '\ntest completed successfully\n'




