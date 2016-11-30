#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/
cd ${HOME}

./dict/test.sh
./avl/test.sh
./bst/test.sh
./digital/test.sh       # currently have failures
./evaluator/test.sh

cd ${DIR}
echo '\nAll scheme tests completed succesfully\n'




