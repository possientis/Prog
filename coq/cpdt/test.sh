#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/cpdt
cd ${HOME}
echo
echo "testing cpdt..."

make 
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




