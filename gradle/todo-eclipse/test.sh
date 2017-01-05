#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/todo-eclipse
cd ${HOME}

gradle eclipse        # generate eclipse config files
gradle cleanEclipse   # removes eclipse config files

cd ${DIR}
echo '\ntest completed successfully\n'




