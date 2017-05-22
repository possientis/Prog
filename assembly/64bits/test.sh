#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly/64bits
cd ${HOME}
option=$(sh option.sh)

# hello world
./hello/test.sh

# intel syntax
./yasm.sh register.asm; ld register.o; ./a.out; ./clean.sh

# at&t syntax
./as.sh  register.s; ld register.o; ./a.out; ./clean.sh

# calls from C and C++
./extern/test.sh

# testing assembly multiplication semantics
./mul/test.sh

# testing carry 
./carry/test.sh

# testing isa
./isa/test.sh

cd ${DIR}
echo
echo "64 bits tests completed successfully"
echo




