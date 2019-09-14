#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/hol
cd ${HOME}
echo
echo "testing hol..."

# Holmake testTheory.uo
# ./clean.sh

./euclid/test.sh
./parity/test.sh

cd ${DIR}
echo '\nAll hol tests completed successfully\n'




