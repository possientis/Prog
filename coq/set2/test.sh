#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/set2
cd ${DIR}
echo
echo "testing set2..."

make -j$(nproc --all) 
./clean.sh

echo '\ntest completed successfully\n'
