#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/javascript/
cd ${HOME}

node node.js
echo '\nnodejs test completed succesfully\n'

./bitcoin/test.sh

cd ${DIR}
echo '\nAll javascript tests completed succesfully\n'




