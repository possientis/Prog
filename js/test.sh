#!/bin/sh
# need to install nodejs (which may not be a debian package)

set -e 
DIR=${HOME}/Prog/js/
cd ${DIR}

node node.js
echo '\nnodejs test completed successfully\n'

#./bitcoin/test.sh
./crypt/test.sh

echo '\nAll javascript tests completed successfully\n'
