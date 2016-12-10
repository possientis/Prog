#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/python/
cd ${HOME}

./bitcoin/test.sh

cd ${DIR}
echo '\nAll python tests completed successfully\n'




