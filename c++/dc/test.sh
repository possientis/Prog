#!/bin/sh

set -e 
DIR=/home/john/Prog/c++/dc
cd ${DIR}

make
./dc
make clean

echo '\ntest completed successfully\n'
