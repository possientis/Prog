#!/bin/sh

set -e 
DIR=/home/john/Prog/c/
cd ${DIR}

#./bitcoin/test.sh
./dict/test.sh
#./dlopen/test.sh
./execve/test.sh
./gcov/test.sh
./library/test.sh
./link/test.sh
./pragma/test.sh

echo '\nAll c tests completed successfully\n'
