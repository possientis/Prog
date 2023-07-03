#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=${HOME}/Prog/agda/vfpa  # changing 'HOME' is a bad idea
cd ${HOME1}
echo
echo "testing vfpa..."

make -j$(nproc --all)
./clean.sh

cd ${DIR}
echo
echo 'All vfpa tests completed successfully'
echo



