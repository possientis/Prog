#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make/mars
cd ${HOME}

./autogen.sh
./configure
make
cd src
./mars  # so it will pick up module.so in current directory
cd ..
make check
make clean
./clean.sh



cd ${DIR}
echo '\ntest completed successfully\n'




