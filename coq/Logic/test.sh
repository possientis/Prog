#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/Logic
cd ${DIR}

echo
echo "testing Logic Coq formalization..."
echo

make -j$(nproc --all)
./clean.sh

echo
echo 'test completed successfully'
echo
