#!/bin/sh

set -e 
DIR=`pwd`
HOME=${HOME}/Prog/scheme/digital/simple
cd ${HOME}

scm -b -f binary-test.scm
scm -b -f bus-test.scm
scm -b -f wire-test.scm

cd ${DIR}
echo '\ntest completed successfully\n'




