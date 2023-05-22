#!/bin/sh

set -e 
DIR=${HOME}/Prog/c++/stl
cd ${DIR}

g++ --std=c++14 remove_copy.cpp
./a.out
rm a.out

echo '\ntest completed successfully\n'




