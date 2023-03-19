#!/bin/sh

set -e 
DIR=/home/john/Prog/coq/Logic
cd ${DIR}

echo
echo "testing Logic Coq formalization..."
echo

make -j2
./clean.sh

echo
echo 'test completed successfully'
echo
