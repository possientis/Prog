#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/
cd ${HOME}

./ijvm/test.sh
./jdbc/test.sh
./bitcoin/test.sh

cd ${DIR}
echo '\nAll java tests completed succesfully\n'




