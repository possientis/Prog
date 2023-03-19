#!/bin/sh

set -e 
DIR=/home/john/Prog/gradle/Rocks
cd ${DIR}

gradle gT

echo '\ntest completed successfully\n'
