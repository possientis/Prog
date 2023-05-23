#!/bin/sh

set -e 
DIR=${HOME}/Prog/gradle/dependency/
cd ${DIR}

gradle third

echo '\ntest completed successfully\n'
