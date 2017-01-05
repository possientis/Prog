#!/bin/sh
# need to create symlink to lib/gradle.sh in /usr/local/bin called 'gradle' 
# need to set up gradle.properties

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle
cd ${HOME}

cat /home/john/.gradle/gradle.properties | grep 'org\.gradle\.daemon=true'

./Hello/test.sh
./Rocks/test.sh
./todo-app/test.sh
./todo-webapp/test.sh
./todo-multi/test.sh
./todo-eclipse/test.sh
./props/test.sh
./wrapper/test.sh
./dependency/test.sh
./pogo/test.sh
./ant/test.sh
./maven/test.sh

cd ${DIR}
echo '\nAll gradle tests completed successfully\n'




