#!/bin/sh

set -e 
DIR=/home/john/Prog/coq/set2
cd ${DIR}
echo
echo "testing set2..."

make; ./clean.sh

echo '\ntest completed successfully\n'
