#!/bin/sh

set -e 
DIR=${HOME}/Prog/hol/euclid
cd ${DIR}
echo
echo "testing euclid theory..."

Holmake
./clean.sh

echo '\ntest completed successfully\n'




