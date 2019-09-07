#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/hol/euclid
cd ${HOME}
echo
echo "testing euclid theory..."

Holmake
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




