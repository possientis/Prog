#!/bin/sh

set -e 
DIR=${HOME}/Prog/scheme/dict
cd ${DIR}

scm -b -f dict-test.scm

echo '\ntest completed successfully\n'
