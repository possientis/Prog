#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/hol/parity
cd ${HOME}
echo
echo "testing parity theory..."

Holmake
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




