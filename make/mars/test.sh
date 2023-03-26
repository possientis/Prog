#!/bin/sh

set -e 
DIR=/home/john/Prog/make/mars
cd ${DIR}

./autogen.sh
./configure
make
cd src
./mars  # so it will pick up module.so in current directory
cd ..
make check
make clean
./clean.sh

echo '\ntest completed successfully\n'
