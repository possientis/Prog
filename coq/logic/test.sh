#!/bin/sh

LOC=/home/john/Prog/coq/logic

set -e 
cd ${LOC}

echo
echo "testing logic Coq formalization..."
echo

make
./clean.sh

echo
echo 'test completed successfully'
echo




