#!/bin/sh

set -e 
DIR=/home/john/Prog/scheme/bst
cd ${DIR}

scm -b -f bst-node-test.scm
scm -b -f bst-test.scm

echo '\ntest completed successfully\n'
