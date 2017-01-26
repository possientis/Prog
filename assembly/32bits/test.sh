#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/32bits
cd ${HOME}

./write-prog.sh
./read-prog.sh
./add-year.sh
./helloworld-lib.sh
./run.sh helloworld-nolib
./printf-example.sh
./conversion-program.sh

./clean.sh


cd ${DIR}
echo '\n32 bits tests completed successfully\n'




