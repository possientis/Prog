#!/bin/sh

DIR=/home/john/Prog/coq/Logic

set -e 
cd ${DIR}

echo
echo "testing Logic Coq formalization..."
echo

make
./clean.sh

echo
echo 'test completed successfully'
echo




