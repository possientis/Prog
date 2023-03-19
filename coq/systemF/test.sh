#!/bin/sh

set -e 
DIR=/home/john/Prog/coq/systemF
cd ${DIR}
echo
echo "testing system F ..."

make; ./clean.sh

echo '\ntest completed successfully\n'
