#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/idris
cd ${HOME}
echo
echo "testing idris..."
echo

echo "Hello world..."
idris Hello.idr --check

echo "Matrix..."
idris Matrix.idr --check

./clean.sh

cd ${DIR}
echo '\nAll idris tests completed successfully\n'




