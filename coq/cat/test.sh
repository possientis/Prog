#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/cat
cd ${HOME}
echo
echo "testing categories ..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




