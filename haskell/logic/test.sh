#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/haskell/logic
cd ${HOME}
echo

echo "testing logic"

./fopl/test.sh
./lambda/test.sh

cd ${DIR}
echo '\nAll logic tests completed successfully\n'




