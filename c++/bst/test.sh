#!/bin/sh

set -e 
DIR=${HOME}/Prog/c++/bst
cd ${DIR}

make
./bst
make clean

echo '\ntest completed successfully\n'
