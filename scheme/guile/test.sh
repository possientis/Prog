#!/bin/sh
# need to install guile-2.2
# may also need to set up symlink in /usr/include 

set -e 
DIR=/home/john/Prog/scheme/guile
cd ${DIR}

export GUILE_AUTO_COMPILE=0

echo
echo "testing simple guile call ..."
guile -s hello.scm
echo

echo "testing creation of guile executable from c source ..."
gcc -c simple-guile.c $(pkg-config --cflags guile-2.2)
gcc simple-guile.o $(pkg-config --libs guile-2.2)
echo

echo "running custom executable ..."
./a.out -s hello.scm
echo

# extending guile with shared library
echo "testing extension of guile from custom shared library ..."
gcc $(pkg-config --cflags guile-2.2) -shared -o libguile-bessel.so -fPIC bessel.c
guile -s bessel1.scm   # running shared library
echo


# calling simple batch
echo "testing calling guile as simple batch ..."
./guile.scm
echo


# using library module example
echo "testing use of library module ..."
guile -s pipe.scm
echo

# defining library module example
# guile must be able to locate module foo/bar-module: create symlink of bar-module.scm
# into /usr/share/guile/2.2/foo
echo "testing use of custom module ..."
guile -s test-module.scm  
echo



# testing extended module
# guile must be able to locate module math/bessel: create symlink of bessel.scm
# into /usr/share/guile/2.2/math
# guile must also be able to locate the share library libguile-bessel 
# create symlink of libguile-bessel.so into /usr/lib/x86_64-linux-gnu/guile/2.2/extensions/
echo "testing use of module created from shared library ..."
guile -s test-bessel.scm
echo

./clean.sh

echo '\nguile tests completed successfully\n'
