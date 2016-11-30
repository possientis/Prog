#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/digital/simple
cd ${HOME}

scm -b -f binary-test.scm
scm -b -f bus-test.scm
scm -b -f wire-test.scm

cd ${DIR}
echo '\ntest completed succesfully\n'




