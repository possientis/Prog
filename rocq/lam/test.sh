#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq/lam
cd ${DIR}
echo
echo "testing lambda calculus..."

make -j$(nproc --all)
./clean.sh

echo '\ntest completed successfully\n'
