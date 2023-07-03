#!/bin/sh
# need to install packages make automake libtool

set -e 
DIR=${HOME}/Prog/make
cd ${DIR}

make -j$(nproc --all)
cat *.tmp
./clean.sh

echo '\nAll make tests completed successfully\n'
