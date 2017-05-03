#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/set
cd ${HOME}
echo
echo "testing set..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




