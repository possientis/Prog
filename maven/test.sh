#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/maven/
cd ${HOME}

./simple/test.sh
./simple-weather/test.sh
./simple-webapp/test.sh
./simple-parent/test.sh
./parent/test.sh

cd ${DIR}
echo '\nAll maven tests completed succesfully\n'




