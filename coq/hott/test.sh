#!/bin/sh

set -e 
DIR=/home/john/Prog/coq/hott
cd ${DIR}
echo
echo "testing set hierarchy ..."

make; ./clean.sh

echo '\ntest completed successfully\n'
