#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq/hott
cd ${DIR}
echo
echo "testing set hierarchy ..."

make -j$(nproc --all)
./clean.sh

echo '\ntest completed successfully\n'
