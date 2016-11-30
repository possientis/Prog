#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/dict
cd ${HOME}

scm -b -f dict-test.scm

cd ${DIR}
echo '\ntest completed succesfully\n'




