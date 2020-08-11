#!/bin/sh
# need to install agda

set -e 
DIR=/home/john/Prog/agda/plfa  # changing 'HOME' is a bad idea
cd ${DIR}
echo
echo "testing plfa..."

make -j2
./clean.sh

echo
echo 'All plfa tests completed successfully'
echo



