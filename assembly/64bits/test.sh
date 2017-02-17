#!/bin/sh
# need to install packages gcc-multilib and g++-multilib

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}

# using the C library requires linking with gcc after compiling with yasm or as.
# However on debian stretch gcc will fail on the object file produced by the
# assemblers, unless the '-no-pie' option is used (no position independent code).
# In order for this script to work both on debian stretch and debian jessie,
# we need to introduce a variable 'option' and set it to "-no-pie" for stretch

version=`uname -a | cut -d' ' -f 7 | cut -d '.' -f 1`
if [ "$version" = "4" ]   # debian stretch 
then
  option="-no-pie"
elif [ "$version" = "3" ] # debian jessie
then
  option=""
else
  echo "unsupported version"
  exit 1
fi

# hello world
./hello/test.sh

# intel syntax
./yasm.sh exit; ld exit.o; ./a.out; ./clean.sh             #_start
./yasm.sh memory; gcc memory.o; ./a.out; ./clean.sh        # main , no c lib
./yasm.sh register; ld register.o; ./a.out; ./clean.sh
./array_build.sh; ./array 20; ./clean.sh


# at&t syntax
./as.sh  register; ld register.o; ./a.out; ./clean.sh


cd ${DIR}
echo
echo "64 bits tests completed successfully"
echo




