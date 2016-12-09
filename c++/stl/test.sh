#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c++/stl
cd ${HOME}

g++ --std=c++14 remove_copy.cpp
./a.out
rm a.out

cd ${DIR}
echo '\ntest completed successfully\n'




