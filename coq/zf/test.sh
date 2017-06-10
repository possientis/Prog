#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/zf
cd ${HOME}
echo
echo "testing ZF..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




