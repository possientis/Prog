#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/evaluator
cd ${HOME}

echo 'starting scheme evaluator unit test ...'
./depend.sh
scm -b -f unit-test.scm

cd ${DIR}
echo '\nscheme evaluator unit test completed successfully\n'




