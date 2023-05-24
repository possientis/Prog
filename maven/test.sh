#!/bin/sh
# need to install package maven

set -e 
DIR=${HOME}/Prog/maven/
cd ${DIR}

# ./simple/test.sh          (broken)
# ./simple-weather/test.sh  (broken)
#./simple-webapp/test.sh
# ./simple-parent/test.sh   (broken)
./parent/test.sh

echo '\nAll maven tests completed successfully\n'
