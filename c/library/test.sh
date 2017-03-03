#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/library
cd ${HOME}
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

cd ${DIR}
echo '\ntest completed successfully\n'




