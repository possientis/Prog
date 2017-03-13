#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/make/guile
cd ${HOME}

./autogen.sh
./configure
make
./simple-guile -s hello.scm 2> /dev/null
./clean.sh



cd ${DIR}
echo '\ntest completed successfully\n'




