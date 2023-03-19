#!/bin/sh

set -e 
DIR=/home/john/Prog/c/library
cd ${DIR}
echo

echo "testing static library use"
sh script_static.sh
echo

echo "testing shared library use"
sh script_shared.sh
echo

echo "testing dynamic loading of shared library"
sh script_dynamic.sh
echo

./clean.sh

echo '\ntest completed successfully\n'




