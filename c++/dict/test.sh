#!/bin/sh

set -e 
DIR=${HOME}/Prog/c++/dict
cd ${DIR}

make
./dict
make clean

echo '\ntest completed successfully\n'
