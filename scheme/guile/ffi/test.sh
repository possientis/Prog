#!/bin/sh

set -e 
DIR=`pwd`
HOME=${HOME}/Prog/scheme/guile/ffi
cd ${HOME}

export GUILE_AUTO_COMPILE=0


# extending guile with shared library
# create symlink of libforeign.so into 
# /usr/lib/x86_64-linux-gnu/guile/2.2/extensions/
echo "testing foreign function interface ..."
gcc -shared -o libforeign.so -fPIC foreign.c
echo


#./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




