#!/bin/sh

set -e 
DIR=${HOME}/Prog/make/jupiter
cd ${DIR}

./autogen.sh
./configure
make
./src/jupiter
make check
make clean
./clean.sh

echo '\ntest completed successfully\n'
