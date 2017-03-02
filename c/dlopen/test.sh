#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/dlopen
cd ${HOME}

# creating shared library which exposes function 'foo'
gcc -shared -o libfoo.so foo.c

# compiling and linking program. Linker need not know about libfoo.so
gcc dlopen.c -ldl

# program opens shared library at runtime
./a.out; ./clean.sh


cd ${DIR}
echo '\ndlopen test completed successfully\n'




