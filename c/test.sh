#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/
cd ${HOME}

./bitcoin/test.sh
./dict/test.sh
./dlopen/test.sh
./execve/test.sh
./gcov/test.sh
./library/test.sh
./link/test.sh
./pragma/test.sh

cd ${DIR}
echo '\nAll c tests completed successfully\n'




