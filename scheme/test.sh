#!/bin/sh
# need to install scm

set -e 
DIR=${HOME}/Prog/scheme/
cd ${DIR}


./avl/test.sh
./bst/test.sh
./dict/test.sh
./digital/test.sh       # currently have failures
./evaluator/test.sh
./guile/test.sh
./hash/test.sh
./stream/test.sh
./types/test.sh

echo '\nAll scheme tests completed successfully\n'
