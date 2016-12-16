#!/bin/sh
# need to install packages ant junit

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ant/
cd ${HOME}

./Available/test.sh
./Env/test.sh
./ExecTask/test.sh
./GettingStarted/test.sh
./JavaTask/test.sh
./Lucene/test.sh

cd ${DIR}
echo '\nAll ant tests completed successfully\n'




