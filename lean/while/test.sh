#!/bin/sh

set -e 
DIR=${HOME}/Prog/lean/while
cd ${DIR}

echo
echo "testing while..."
echo

make
./clean.sh
 
echo
echo 'while completed successfully'
echo
