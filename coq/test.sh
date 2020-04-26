#!/bin/sh

LOC=/home/john/Prog/coq

set -e 
cd ${LOC}

echo
echo "testing coq..."
echo

./set/test.sh
./set2/test.sh
./zf/test.sh
./sf/test.sh
./cat/test.sh
./hott/test.sh
./systemF/test.sh
./lam/test.sh
./cpdt/test.sh
./logic/test.sh

./clean.sh

echo
echo 'All coq tests completed successfully'
echo




