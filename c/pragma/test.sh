#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/pragma
cd ${HOME}


# running program without foo override
gcc weak.c; ./a.out; ./clean.sh

# running program with foo override
gcc -c foo.c; gcc weak.c foo.o; ./a.out; ./clean.sh

# running program without definition of 'debug'
gcc unresolved.c; ./a.out; ./clean.sh

# running program with debug function provided
gcc -c debug.c; gcc unresolved.c debug.o; ./a.out; ./clean.sh

cd ${DIR}
echo '\npragma test completed successfully\n'




