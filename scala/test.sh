#!/bin/sh

set -e 
DIR=/home/john/Prog/scala
cd ${DIR}

scalac HelloWorld.scala
scala HelloWorld
./clean.sh

echo '\nAll scala tests completed successfully\n'
