#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/avl
cd ${HOME}

scm -b -f avl-node-test.scm
scm -b -f avl-test.scm

cd ${DIR}
echo '\ntest completed successfully\n'




