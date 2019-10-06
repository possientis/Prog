#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda/vfpa  # changing 'HOME' is a bad idea
cd ${HOME1}
echo
echo "testing vfpa..."

make

./clean.sh

cd ${DIR}
echo '\nAll vfpa tests completed successfully\n'




