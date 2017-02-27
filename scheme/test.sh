#!/bin/sh
# need to install scm

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/
cd ${HOME}


./guile/test.sh
./dict/test.sh
./avl/test.sh
./bst/test.sh
./digital/test.sh       # currently have failures
./hash/test.sh
./stream/test.sh
./evaluator/test.sh

cd ${DIR}
echo '\nAll scheme tests completed successfully\n'




