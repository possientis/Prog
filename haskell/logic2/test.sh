#!/bin/sh

set -e 
DIR=${HOME}/Prog/haskell/logic2
cd ${DIR}
echo

echo "testing logic"

./fopl/test.sh
./lambda/test.sh

echo '\nAll logic tests completed successfully\n'
