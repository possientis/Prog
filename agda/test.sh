#!/bin/sh
# need to install agda

set -e 
DIR=${HOME}/Prog/agda
cd ${DIR}

echo
echo 'testing agda'
echo

#echo
#echo "testing agda hello world..."
#agda --compile -v0 hello-world.agda
#./hello-world
#./clean.sh
#echo "hello world test completed successfully"
#echo

make -j$(nproc --all)
./clean.sh

echo
echo 'All agda tests completed successfully'
echo



