#!/bin/sh

set -e 
DIR=/home/john/Prog/scheme/avl
cd ${DIR}

scm -b -f avl-node-test.scm
scm -b -f avl-test.scm

echo '\ntest completed successfully\n'
