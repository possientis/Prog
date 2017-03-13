#!/bin/sh
# need to install packages make automake libtool

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make
cd ${HOME}

./guile/test.sh
./jupiter/test.sh
./saturn/test.sh
./mars/test.sh


cd ${DIR}
echo '\nAll make tests completed successfully\n'




