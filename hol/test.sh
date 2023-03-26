#!/bin/sh

set -e 
DIR=/home/john/Prog/hol
cd ${DIR}
echo
echo "testing hol..."

# Holmake testTheory.uo
# ./clean.sh

./euclid/test.sh
./parity/test.sh

echo '\nAll hol tests completed successfully\n'
