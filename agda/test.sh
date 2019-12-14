#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda  # changing 'HOME' is a bad idea
cd ${HOME1}

./vfpa/test.sh
./plfa/test.sh

agda --compile hello-world.agda
./hello-world
./clean.sh

cd ${DIR}
echo '\nAll agda tests completed successfully\n'




