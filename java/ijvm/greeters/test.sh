#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/ijvm/greeters
cd ${HOME}

echo 'building ...'
./clean.sh
./build.sh


echo 'running ...'
cd build
./run.sh
cd ..

echo 'cleaning ...'
./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




