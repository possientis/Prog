#!/bin/sh

set -e 
DIR=/home/john/Prog/c/gcov
cd ${DIR}
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

echo '\ntest completed successfully\n'




