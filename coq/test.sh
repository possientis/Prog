#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq
cd ${HOME}

coqtop -batch -lv sort.v -I Lib


cd ${DIR}
echo '\nAll coq tests completed succesfully\n'




