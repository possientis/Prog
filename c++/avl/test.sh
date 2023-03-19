#!/bin/sh

set -e 
DIR=/home/john/Prog/c++/avl
cd ${DIR}

make
./avl
make clean

echo '\ntest completed successfully\n'
