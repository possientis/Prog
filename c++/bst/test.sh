#!/bin/sh

set -e 
DIR=/home/john/Prog/c++/bst
cd ${DIR}

make
./bst
make clean

echo '\ntest completed successfully\n'




