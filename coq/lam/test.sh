#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/lam
cd ${DIR}
echo
echo "testing lambda calculus..."

make -j$(nproc --all)
./clean.sh

echo '\ntest completed successfully\n'
