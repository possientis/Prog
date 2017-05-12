#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/sed/
cd ${HOME}
echo 
echo "testing sed..."

sed -f distros.sed distros.txt

cd ${DIR}
echo '\nAll sed tests completed successfully\n'




