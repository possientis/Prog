#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/hott
cd ${DIR}
echo
echo "testing set hierarchy ..."

make; ./clean.sh

echo '\ntest completed successfully\n'
