#!/bin/sh

set -e 
DIR=/home/john/Prog/make/guile
cd ${DIR}

./autogen.sh
./configure
make
./simple-guile -s hello.scm 2> /dev/null
./clean.sh

echo '\ntest completed successfully\n'
