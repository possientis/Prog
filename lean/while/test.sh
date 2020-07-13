#!/bin/sh

LOC=/home/john/Prog/lean/while
set -e 
cd ${LOC}

echo
echo "testing while..."
echo

make
./clean.sh
 
echo
echo 'while completed successfully'
echo
