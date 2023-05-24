#!/bin/sh

set -e 
DIR=${HOME}/Prog/scala
cd ${DIR}

scalac HelloWorld.scala
scala HelloWorld
./clean.sh

echo '\nAll scala tests completed successfully\n'
