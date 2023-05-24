#!/bin/sh

set -e 
DIR=${HOME}/Prog/scheme/hash
cd ${DIR}

scm -b -f hash-test.scm

echo '\ntest completed successfully\n'
