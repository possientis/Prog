#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq/zf
cd ${DIR}
echo
echo "testing ZF..."

make -j$(nproc --all) 
./clean.sh

echo '\ntest completed successfully\n'
