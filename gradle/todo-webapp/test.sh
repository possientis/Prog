#!/bin/sh

set -e 
DIR=${HOME}/Prog/gradle/todo-webapp
cd ${DIR}

gradle build
# not testing program
gradle clean

echo '\ntest completed successfully\n'
