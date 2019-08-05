#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/idris
cd ${HOME}
echo
echo "testing idris..."

idris Hello.idr -o Hello
./Hello
./clean.sh

cd ${DIR}
echo '\nAll idris tests completed successfully\n'




