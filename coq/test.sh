#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/coq
cd ${HOME}
echo
echo "testing coq..."

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

cd ${DIR}
echo '\nAll coq tests completed successfully\n'




