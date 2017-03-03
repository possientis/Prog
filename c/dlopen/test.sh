#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/dlopen
cd ${HOME}
echo

# creating shared library which exposes function 'foo'
# defining a soname here for the sake of it, not actually using it
echo "creating shared library libfoo.so"
gcc -shared -fPIC -Wl,-soname,libfoo.so.1 -o libfoo.so foo.c
echo

# compiling and linking program. Linker need not know about libfoo.so
echo "compiling and linking program"
gcc dlopen.c -ldl
echo

# program opens shared library at runtime
echo "testing dynamic loading of libfoo.so"
./a.out; ./clean.sh
echo

# testing cos(2)
echo "testing dynamic loading of cosine function"
gcc -ldl cosine.c; ./a.out; ./clean.sh
echo


cd ${DIR}
echo '\ndlopen test completed successfully\n'




