#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda/plfa  # changing 'HOME' is a bad idea
cd ${HOME1}
echo
echo "testing plfa..."

agda test.agda
agda induction.agda

./clean.sh

cd ${DIR}
echo '\nAll plfa tests completed successfully\n'




