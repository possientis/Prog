#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/scala
cd ${HOME}

scalac HelloWorld.scala
scala HelloWorld
./clean.sh

cd ${DIR}
echo '\nAll scala tests completed successfully\n'




