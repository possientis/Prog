#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/sf/Imp
cd ${HOME}
echo
echo "testing Imp ..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




