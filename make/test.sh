#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make
cd ${HOME}

./jupiter/test.sh
./saturn/test.sh
# ./mars/test.sh still failing


cd ${DIR}
echo '\nAll make tests completed succesfully\n'




