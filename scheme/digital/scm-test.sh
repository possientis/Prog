#!/bin/sh
# unit testing run as batch file rather scm program
# this is to allow each component to be loaded separately
# so as to ensure it does not have dependencies other
# than those explicitely indicated by the top 'load' statement

echo "\n"
echo Starting digital unit testing ...
scm "queue-test.scm"
scm "agenda-test.scm"
scm "global-test.scm"
scm "wire-test.scm"
scm "source-test.scm"
scm "connect-test.scm"
scm "transistor-test.scm"
scm "gate-not-test.scm"
scm "gate-nor-test.scm"
scm "gate-nand-test.scm"
