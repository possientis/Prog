#!/bin/sh
# need to install agda

set -e 
DIR=${HOME}/Prog/agda/aop
cd ${DIR}
echo
echo "testing aop..."

agda filter.agda
./clean.sh

echo
echo 'All aop tests completed successfully'
echo
