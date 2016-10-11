#!/bin/sh
# unit testing run as batch file rather scm program
# this is to allow each component to be loaded separately
# so as to ensure it does not have dependencies other
# than those explicitely indicated by the top 'load' statement

echo "\n"
echo Starting digital unit testing ...
mit-scheme --quiet --load "queue-test.scm"
mit-scheme --quiet --load "agenda-test.scm"
mit-scheme --quiet --load "global-test.scm"
mit-scheme --quiet --load "wire-test.scm"
#mit-scheme --quiet --load "source-test.scm"
mit-scheme --quiet --load "connect-test.scm"
mit-scheme --quiet --load "transistor-test.scm"
mit-scheme --quiet --load "gate-not-test.scm"
mit-scheme --quiet --load "gate-nor-test.scm"
mit-scheme --quiet --load "gate-nand-test.scm"
