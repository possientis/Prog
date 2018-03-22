#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq/sf
cd ${HOME}
echo
echo "testing software foundations..."

make; ./clean.sh

cd ${DIR}
echo '\ntest completed successfully\n'




