#!/bin/sh

set -e 
DIR=/home/john/Prog/gradle/ant
cd ${DIR}

gradle hello
gradle antTask

echo '\ntest completed successfully\n'
