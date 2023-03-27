#!/bin/sh

set -e 
DIR=/home/john/Prog/tex/
cd ${DIR}
echo

echo "testing tex documents..."

./Logic/test.sh

echo

echo '\nAll tex tests completed successfully\n'
