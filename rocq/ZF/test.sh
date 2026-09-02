#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq/ZF
cd ${DIR}

echo
echo "testing ZF Coq formalization..."
echo

make -j$(nproc --all)
./clean.sh

echo
echo 'test completed successfully'
echo
