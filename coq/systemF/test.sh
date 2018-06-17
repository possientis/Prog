#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/systemF
cd ${HOME}
echo
echo "testing system F ..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




