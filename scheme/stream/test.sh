#!/bin/sh

set -e 
DIR=/home/john/Prog/scheme/stream
cd ${DIR}

scm -b -f stream-test.scm

echo '\ntest completed successfully\n'
