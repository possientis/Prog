#!/bin/sh

set -e 
DIR=${HOME}/Prog/java/gcj
cd ${DIR}

gcj=$(sh gcj.sh)

$gcj --main=HelloWorld HelloWorld.java 
./a.out 
./clean.sh

echo '\ngcj test completed successfully\n'
