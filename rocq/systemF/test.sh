#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq/systemF
cd ${DIR}
echo
echo "testing system F ..."

make -j$(nproc --all)
./clean.sh

echo '\ntest completed successfully\n'
