#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make/jupiter
cd ${HOME}

./autogen.sh
./configure
make
./src/jupiter
make check
make clean
./clean.sh



cd ${DIR}
echo '\ntest completed successfully\n'




