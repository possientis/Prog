#/bin/sh

set -e 
DIR=${HOME}/Prog/c/bitcoin
cd ${DIR}

./secp256k1/test.sh

echo '\nbitcoin tests completed successfully\n'




