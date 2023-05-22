#!/bin/sh

set -e 
DIR=${HOME}/Prog/c++/dc
cd ${DIR}

make
./dc
make clean

echo '\ntest completed successfully\n'
