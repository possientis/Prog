#!/bin/sh

set -e 
DIR=/home/john/Prog/coq/zf
cd ${DIR}
echo
echo "testing ZF..."

make; ./clean.sh

echo '\ntest completed successfully\n'
