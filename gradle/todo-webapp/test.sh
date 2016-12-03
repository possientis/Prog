#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/todo-webapp
cd ${HOME}

gradle build
# not testing program
gradle clean

cd ${DIR}
echo '\ntest completed succesfully\n'




