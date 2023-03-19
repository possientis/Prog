#!/bin/sh

set -e 
DIR=/home/john/Prog/gradle/wrapper
cd ${DIR}

gradle wrapper
./clean.sh

echo '\ntest completed successfully\n'
