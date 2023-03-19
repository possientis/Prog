#!/bin/sh

set -e 
DIR=/home/john/Prog/gradle/dependency/
cd ${DIR}

gradle third

echo '\ntest completed successfully\n'
