#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/assembly
cd ${HOME}

./write-prog.sh
./read-prog.sh
./add-year.sh
rm test.dat
rm testout.dat

./helloworld-lib.sh
./run.sh helloworld-nolib
./printf-example.sh
./conversion-program.sh


cd ${DIR}
echo '\nassembly tests completed successfully\n'




