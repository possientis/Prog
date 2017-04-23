#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/types
cd ${HOME}
echo
echo "testing simple evaluator..."

scm unit-test.scm

cd ${DIR}
echo '\ntest completed successfully\n'




