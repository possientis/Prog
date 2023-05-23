#!/bin/sh

set -e 
DIR=${HOME}/Prog/gradle/wrapper
cd ${DIR}

gradle wrapper
./clean.sh

echo '\ntest completed successfully\n'
