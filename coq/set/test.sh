#!/bin/sh

LOC=/home/john/Prog/coq/set

set -e 
cd ${LOC}

echo
echo "testing set..."
echo

make 

./clean.sh

echo
echo 'test completed successfully'
echo




