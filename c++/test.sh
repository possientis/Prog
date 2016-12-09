#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c++/
cd ${HOME}

./avl/test.sh
./bst/test.sh
./dc/test.sh
./link/test.sh
./dict/test.sh
./stl/test.sh
./bitcoin/test.sh

cd ${DIR}
echo '\nAll c++ tests completed successfully\n'




