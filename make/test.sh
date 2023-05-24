#!/bin/sh
# need to install packages make automake libtool

set -e 
DIR=${HOME}/Prog/make
cd ${DIR}

./guile/test.sh
./jupiter/test.sh
./saturn/test.sh
./mars/test.sh

echo '\nAll make tests completed successfully\n'
