#!/bin/sh

set -e 
DIR=/home/john/Prog/asm/64bits
cd ${DIR}

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

echo
echo "64 bits tests completed successfully"
echo




