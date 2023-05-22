#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq/sf
cd ${DIR}
echo
echo "testing software foundations..."

make; ./clean.sh

echo '\ntest completed successfully\n'
