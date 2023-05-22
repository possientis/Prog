#!/bin/sh

set -e 
DIR=${HOME}/Prog/c++/avl
cd ${DIR}

make
./avl
make clean

echo '\ntest completed successfully\n'
