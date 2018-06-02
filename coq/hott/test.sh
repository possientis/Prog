#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/hott
cd ${HOME}
echo
echo "testing set hierarchy ..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




