#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/ijvm/
cd ${HOME}

./greeters/test.sh

cd ${DIR}
echo '\nijvm test completed succesfully\n'




