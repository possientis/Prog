#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=${HOME}/Prog/asm
cd ${DIR}

./32bits/test.sh
./64bits/test.sh

echo '\nAll assembly tests completed successfully\n'




