#!/bin/sh

set -e 
DIR=${HOME}/Prog/coq
cd ${DIR}

echo
echo "testing coq..."
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
echo 'All coq tests completed successfully'
echo
