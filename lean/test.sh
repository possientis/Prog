#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/lean
cd ${HOME}
echo
echo "testing lean..."

lean classical.lean

# clean up
./clean.sh
 
cd ${DIR}
echo '\nAll lean tests completed successfully\n'




