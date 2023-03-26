#!/bin/sh

set -e 
DIR=/home/john/Prog/scheme/digital
cd ${DIR}

scm -b -f queue-test.scm
scm -b -f agenda-test.scm
scm -b -f global-test.scm
scm -b -f wire-test.scm
scm -b -f source-test.scm
scm -b -f connect-test.scm
scm -b -f transistor-test.scm
scm -b -f gate-not-test.scm
scm -b -f gate-nor-test.scm     # currently have failures
scm -b -f gate-nand-test.scm    # currently have failures

./simple/test.sh

echo '\ndigital tests completed successfully\n'
