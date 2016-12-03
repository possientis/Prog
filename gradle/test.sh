#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle
cd ${HOME}

cat /home/john/.gradle/gradle.properties | grep 'org\.gradle\.daemon=true'

./Hello/test.sh
./Rocks/test.sh
./todo-app/test.sh
./todo-webapp/test.sh

cd ${DIR}
echo '\nAll gradle tests completed succesfully\n'




