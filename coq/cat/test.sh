#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/cat
cd ${DIR}
echo
echo "testing categories ..."

make; ./clean.sh

echo '\ntest completed successfully\n'
