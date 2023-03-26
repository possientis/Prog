#!/bin/sh

set -e 
DIR=/home/john/Prog/scheme/types
cd ${DIR}
echo
echo "testing simple evaluator..."

scm unit-test.scm

echo '\ntest completed successfully\n'
