#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/lam
cd ${HOME}
echo
echo "testing lambda calculus..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




