#!/bin/sh

set -e 
DIR=${HOME}/Prog/clojure/redis
cd ${DIR}


RABBIT_JARS=
for d in ./*.jar
do
    RABBIT_JARS="$d:$RABBIT_JARS"
done

clojurec -cp ${RABBIT_JARS} test_redis 1> /dev/null
java -cp ${RABBIT_JARS} test_redis
./clean.sh

echo '\nredis test completed successfully\n'
