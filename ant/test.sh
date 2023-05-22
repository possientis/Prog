#!/bin/sh
# need to install packages ant junit

set -e 
DIR=${HOME}/Prog/ant/
cd ${DIR}

./Available/test.sh
./AntTask/test.sh
./Env/test.sh
./ExecTask/test.sh
./GettingStarted/test.sh
./JavaTask/test.sh
#./JNI/test.sh
#./Lucene/test.sh
./Script/test.sh

echo '\nAll ant tests completed successfully\n'




