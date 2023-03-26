#!/bin/sh

set -e 
DIR=/home/john/Prog/python/bitcoin
cd ${DIR}
echo

echo "testing ecdsa module ..."
python3 ecdsa_test.py
echo

echo "testing the hashlib module ..."
python3 hashlib_test1.py
python3 hashlib_test2.py
python3 hashlib_test3.py
echo

echo "testing utxo selection ..."
python3 select_utxo.py
echo

#echo "testing pycoin installation ..."
#python3 pycoin_test.py
#echo

#echo "testing ku with private key from Mastering Bitcoin ..."
#ku -j KxFC1jmwwCoACiCAWZ3eXa96mBM6tb3TYzGmf6YwgdGWZgawvrtJ
#echo

echo '\nbitcoin tests completed successfully\n'
