#!/bin/sh

set -e 
DIR=${HOME}/Prog/rocq
cd ${DIR}

echo
echo "testing rocq..."
echo

./Logic/test.sh
./ZF/test.sh
./set2/test.sh
./zf/test.sh
./sf/test.sh
./cat/test.sh
./hott/test.sh
./systemF/test.sh
./lam/test.sh
./CPDT/test.sh

echo
echo 'All rocq tests completed successfully'
echo
