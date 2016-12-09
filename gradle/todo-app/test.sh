#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/todo-app
cd ${HOME}

gradle build
# not testing program
gradle clean

cd ${DIR}
echo '\ntest completed successfully\n'




