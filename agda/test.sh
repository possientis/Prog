#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda  # changing 'HOME' is a bad idea
cd ${HOME1}

echo
echo "testing agda hello world..."
agda --compile -v0 hello-world.agda
./hello-world
./clean.sh
echo "hello world test completed successfully"
echo

./vfpa/test.sh
./plfa/test.sh


cd ${DIR}
echo
echo 'All agda tests completed successfully'
echo



