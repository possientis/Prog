#!/bin/sh

set -e 
DIR=${HOME}/Prog/clojure/rabbitmq
cd ${DIR}


RABBIT_JARS=
for d in ./*.jar
do
    RABBIT_JARS="$d:$RABBIT_JARS"
done

clojurec -cp ${RABBIT_JARS} test_rabbitmq 1> /dev/null
java -cp ${RABBIT_JARS} test_rabbitmq
./clean.sh

echo '\nrabbitmq test completed successfully\n'
