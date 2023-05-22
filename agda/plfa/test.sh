#!/bin/sh

set -e 
DIR=${HOME}/Prog/agda/plfa
cd ${DIR}
echo
echo "testing plfa..."

make
./clean.sh

echo
echo 'All plfa tests completed successfully'
echo
