#!/bin/sh
# need to install nodejs (which may not be a debian package)

set -e 
DIR=`pwd`
HOME=/home/john/Prog/js/
cd ${HOME}

node node.js
echo '\nnodejs test completed successfully\n'

./bitcoin/test.sh

cd ${DIR}
echo '\nAll javascript tests completed successfully\n'




