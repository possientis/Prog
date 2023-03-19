#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=/home/john/Prog/asm/32bits
cd ${DIR}

./write-prog.sh
./read-prog.sh
./add-year.sh
./helloworld-lib.sh
./run.sh helloworld-nolib
./printf-example.sh
./conversion-program.sh

./clean.sh

echo '\n32 bits tests completed successfully\n'




