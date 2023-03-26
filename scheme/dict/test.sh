#!/bin/sh

set -e 
DIR=/home/john/Prog/scheme/dict
cd ${DIR}

scm -b -f dict-test.scm

echo '\ntest completed successfully\n'
