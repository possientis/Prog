#!/bin/sh
# need to install python3-ecdsa

set -e 
DIR=/home/john/Prog/python/
cd ${DIR}

./bitcoin/test.sh

echo '\nAll python tests completed successfully\n'
