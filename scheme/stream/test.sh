#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/stream
cd ${HOME}

scm -b -f stream-test.scm

cd ${DIR}
echo '\ntest completed successfully\n'




