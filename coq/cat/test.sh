#!/bin/sh

set -e 
DIR=/home/john/Prog/coq/cat
cd ${DIR}
echo
echo "testing categories ..."

make; ./clean.sh

echo '\ntest completed successfully\n'
