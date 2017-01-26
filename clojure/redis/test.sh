#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/clojure/redis
cd ${HOME}


RABBIT_JARS=
for d in ./*.jar
do
    RABBIT_JARS="$d:$RABBIT_JARS"
done

clojurec -cp ${RABBIT_JARS} test_redis 1> /dev/null
java -cp ${RABBIT_JARS} test_redis
./clean.sh

cd ${DIR}
echo '\nredis test completed successfully\n'




