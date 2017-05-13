#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/gcov
cd ${HOME}
echo
echo "testing gcov..."
echo

# generates *.gcno files
gcc -fprofile-arcs -ftest-coverage coverage.c

# generates *.gcda files
./a.out > /dev/null

# generates *.gcov files
gcov coverage.c > /dev/null

cat coverage.c.gcov

./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




