#!/bin/sh

set -e 
DIR=/home/john/Prog/coq/lam
cd ${DIR}
echo
echo "testing lambda calculus..."

make; ./clean.sh

echo '\ntest completed successfully\n'
