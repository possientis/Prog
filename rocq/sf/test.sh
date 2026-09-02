#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq/sf
cd ${DIR}
echo
echo "testing software foundations..."

make -j$(nproc --all)
./clean.sh

echo '\ntest completed successfully\n'
