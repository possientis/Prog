#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/hash
cd ${HOME}

scm -b -f hash-test.scm

cd ${DIR}
echo '\ntest completed succesfully\n'




