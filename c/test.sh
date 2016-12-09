#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/
cd ${HOME}

./dict/test.sh
./execve/test.sh
./link/test.sh

cd ${DIR}
echo '\nAll c tests completed successfully\n'




