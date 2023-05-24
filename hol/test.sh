#!/bin/sh

set -e 
DIR=${HOME}/Prog/hol
cd ${DIR}
echo
echo "testing hol..."

# Holmake testTheory.uo
# ./clean.sh

./euclid/test.sh
./parity/test.sh

echo '\nAll hol tests completed successfully\n'
