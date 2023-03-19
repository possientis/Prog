#!/bin/sh

set -e 
DIR=/home/john/Prog/gradle/todo-eclipse
cd ${DIR}

gradle eclipse        # generate eclipse config files
gradle cleanEclipse   # removes eclipse config files

echo '\ntest completed successfully\n'
