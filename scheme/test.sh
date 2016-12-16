#!/bin/sh
# need to install scm

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/
cd ${HOME}

./dict/test.sh
./avl/test.sh
./bst/test.sh
./digital/test.sh       # currently have failures
./evaluator/test.sh
./hash/test.sh
./stream/test.sh

cd ${DIR}
echo '\nAll scheme tests completed successfully\n'




