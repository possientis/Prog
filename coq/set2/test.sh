#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/set2
cd ${HOME}
echo
echo "testing set2..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




