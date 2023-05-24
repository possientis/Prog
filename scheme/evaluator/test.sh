#!/bin/sh

set -e 
DIR=${HOME}/Prog/scheme/evaluator
cd ${DIR}

echo 'starting scheme evaluator unit test ...'
#./depend.sh
scm -b -f unit-test.scm

echo '\nscheme evaluator unit test completed successfully\n'
