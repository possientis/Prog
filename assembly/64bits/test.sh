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

# Hello world!
./as.sh hello_32bits; ld hello_32bits.o; ./a.out; ./clean.sh     # 32 bits at&t
./as.sh hello_syscall; ld hello_syscall.o; ./a.out; ./clean.sh   # 64 bits syscall
./as.sh hello_printf; gcc $option hello_printf.o; ./a.out; ./clean.sh   # c lib
./as.sh hello_write; gcc $option hello_write.o; ./a.out; ./clean.sh     # c lib


./yasm.sh hello_32bits; ld hello_32bits.o; ./a.out; ./clean.sh   # 32 bits int 
./yasm.sh hello_syscall; ld hello_syscall.o; ./a.out; ./clean.sh # 64 bits syscall
./yasm.sh hello_printf; gcc $option hello_printf.o; ./a.out; ./clean.sh  # c lib
./yasm.sh hello_write; gcc $option hello_write.o; ./a.out; ./clean.sh    # c lib

# intel syntax
./yasm.sh exit; ld exit.o; ./a.out; ./clean.sh             #_start
./yasm.sh memory; gcc memory.o; ./a.out; ./clean.sh        # main , no c lib
./yasm.sh register; ld register.o; ./a.out; ./clean.sh
./array_build.sh; ./array 20; ./clean.sh


# at&t syntax
./as.sh  register; ld register.o; ./a.out; ./clean.sh


cd ${DIR}
echo '\n64 bits tests completed successfully\n'




