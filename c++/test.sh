#!/bin/sh

set -e 
DIR=${HOME}/Prog/c++/
cd ${DIR}

./avl/test.sh
./bst/test.sh
./dc/test.sh
./link/test.sh
./dict/test.sh
./stl/test.sh
./bitcoin/test.sh

echo '\nAll c++ tests completed successfully\n'
