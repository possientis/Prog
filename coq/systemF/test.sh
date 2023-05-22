#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/systemF
cd ${DIR}
echo
echo "testing system F ..."

make; ./clean.sh

echo '\ntest completed successfully\n'
