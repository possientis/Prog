#!/bin/sh

HOME=/home/john/Prog/scheme/evaluator/
DIR=`pwd`

cd ${HOME}

scm -b -f unit-test.scm # non-interactively

if [ $? -ne 0 ]
then
  echo "\nSCHEME INTERPRETER UNIT TEST HAS FAILED!!!\n"
  cd ${DIR}
  exit 1
fi

cd ${DIR}
