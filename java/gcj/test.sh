#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/gcj
cd ${HOME}

gcj=$(sh gcj.sh)

$gcj --main=HelloWorld HelloWorld.java 
./a.out 
./clean.sh

cd ${DIR}
echo '\ngcj test completed successfully\n'




