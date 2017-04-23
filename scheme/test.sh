#!/bin/sh
# need to install scm

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/
cd ${HOME}


./avl/test.sh
./bst/test.sh
./dict/test.sh
./digital/test.sh       # currently have failures
./evaluator/test.sh
./guile/test.sh
./hash/test.sh
./stream/test.sh
./types/test.sh

cd ${DIR}
echo '\nAll scheme tests completed successfully\n'




