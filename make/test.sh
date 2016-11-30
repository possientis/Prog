#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make
cd ${HOME}

./jupiter/test.sh
./saturn/test.sh


cd ${DIR}
echo '\n All make tests completed succesfully\n'




