#!/bin/sh

set -e 
DIR=${HOME}/Prog/c++/link
cd ${DIR}

make link
make linknode
./linknode
./link
make clean

echo '\ntest completed successfully\n'




