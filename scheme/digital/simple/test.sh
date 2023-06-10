#!/bin/sh

set -e 
DIR=${HOME}/Prog/scheme/digital/simple
cd ${DIR}

scm -b -f binary-test.scm
scm -b -f bus-test.scm
scm -b -f wire-test.scm

echo '\ntest completed successfully\n'
