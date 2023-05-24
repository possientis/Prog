#!/bin/sh

set -e 
DIR=${HOME}/Prog/sed/
cd ${DIR}
echo 
echo "testing sed..."

sed -f distros.sed distros.txt

echo '\nAll sed tests completed successfully\n'
