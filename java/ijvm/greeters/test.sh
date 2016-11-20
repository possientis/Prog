#!/bin/sh

set -e 

DIR=`pwd`
HOME=/home/john/Prog/java/ijvm/greeters

cd ${HOME}

echo '\nbuilding ...'
./clean.sh
./build.sh


echo '\nrunning ...'
cd build
./run.sh
cd ..

echo '\ncleaning ...'
./clean.sh

cd ${DIR}

echo '\ntest completed succesfully\n'




