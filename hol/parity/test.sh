#!/bin/sh

set -e 
DIR=${HOME}/Prog/hol/parity
cd ${DIR}
echo
echo "testing parity theory..."

Holmake
./clean.sh

echo '\ntest completed successfully\n'




