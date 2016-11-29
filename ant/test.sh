#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ant/
cd ${HOME}

./GettingStarted/test.sh
./Lucene/test.sh
./JavaTask/test.sh

cd ${DIR}
echo '\nAll ant tests completed succesfully\n'




