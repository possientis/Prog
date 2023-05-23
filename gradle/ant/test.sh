#!/bin/sh

set -e 
DIR=${HOME}/Prog/gradle/ant
cd ${DIR}

gradle hello
gradle antTask

echo '\ntest completed successfully\n'
