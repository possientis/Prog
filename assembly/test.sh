#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly
cd ${HOME}

./32bits/test.sh
./64bits/test.sh

cd ${DIR}
echo '\nAll assembly tests completed successfully\n'




