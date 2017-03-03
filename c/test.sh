#!/bin/sh
# need to install package gcc

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/
cd ${HOME}

./dict/test.sh
./execve/test.sh
./link/test.sh
./bitcoin/test.sh
./pragma/test.sh
./dlopen/test.sh
./library/test.sh

cd ${DIR}
echo '\nAll c tests completed successfully\n'




