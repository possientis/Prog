#!/bin/sh

set -e 
DIR=${HOME}/Prog/java/ijvm/greeters
cd ${DIR}

echo 'building ...'
./clean.sh
./build.sh


echo 'running ...'
cd build
./run.sh
cd ..

echo 'cleaning ...'
./clean.sh

echo '\ntest completed successfully\n'




