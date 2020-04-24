#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda/plfa  # changing 'HOME' is a bad idea
cd ${HOME1}
echo
echo "testing plfa..."

make
./clean.sh

cd ${DIR}
echo
echo 'All plfa tests completed successfully'
echo



