#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/bst
cd ${HOME}

scm -b -f bst-node-test.scm
scm -b -f bst-test.scm

cd ${DIR}
echo '\ntest completed succesfully\n'




