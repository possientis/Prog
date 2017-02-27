#!/bin/sh
# need to install guile-2.0
# may also need to set up symlink in /usr/include 

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scheme/guile
cd ${HOME}

export GUILE_AUTO_COMPILE=0

# simple call
guile -s hello.scm

# creating guile from c source
gcc simple-guile.c $(pkg-config --cflags --libs guile-2.0); 
./a.out -s hello.scm

# extending guile with shared library
gcc $(pkg-config --cflags guile-2.0) -shared -o libguile-bessel.so -fPIC bessel.c
guile -s bessel.scm   # running shared library

# calling simple batch
./guile.scm

# module example
guile -s pipe.scm

./clean.sh

cd ${DIR}
echo '\nguile tests completed successfully\n'




