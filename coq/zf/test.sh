#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/zf
cd ${DIR}
echo
echo "testing ZF..."

make -j$(nproc --all) 
./clean.sh

echo '\ntest completed successfully\n'
