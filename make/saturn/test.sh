#!/bin/sh

set -e 
DIR=${HOME}/Prog/make/saturn
cd ${DIR}

./autogen.sh
./configure
make
./src/saturn
make check
make clean
./clean.sh

echo '\ntest completed successfully\n'
