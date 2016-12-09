#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c++/link
cd ${HOME}

make link
make linknode
./linknode
./link
make clean

cd ${DIR}
echo '\ntest completed successfully\n'




