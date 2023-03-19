#!/bin/sh

set -e 
DIR=/home/john/Prog/c++/dict
cd ${DIR}

make
./dict
make clean

echo '\ntest completed successfully\n'
