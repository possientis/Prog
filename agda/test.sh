#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda  # changing 'HOME' is a bad idea
cd ${HOME1}

agda --compile hello-world.agda > /dev/null
./hello-world
./clean.sh

cd ${DIR}
echo '\nAll agda tests completed successfully\n'




