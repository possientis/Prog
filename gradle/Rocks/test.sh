#!/bin/sh

set -e 
DIR=${HOME}/Prog/gradle/Rocks
cd ${DIR}

gradle gT

echo '\ntest completed successfully\n'
