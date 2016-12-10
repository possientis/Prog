#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/python/bitcoin
cd ${HOME}

python3 ecdsa_test.py
python3 hashlib_test1.py
python3 hashlib_test2.py
python3 hashlib_test3.py
python3 select_utxo.py

cd ${DIR}
echo '\nbitcoin tests completed successfully\n'




