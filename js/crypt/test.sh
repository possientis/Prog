#!/bin/sh
# need to install nodejs (which may not be a debian package)

set -e 
DIR=/home/john/Prog/js/crypt
cd ${DIR}
echo
echo "testing crypt..."


node hash.js
node salt.js
node hmac.js
node symmetric-encrypt.js
node keypair.js
node asymmetric-encrypt.js
node sign.js

echo
echo 'All crypt tests completed successfully'
echo
