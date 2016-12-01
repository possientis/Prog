#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/clojure/rabbitmq
cd ${HOME}


RABBIT_JARS=
for d in ./*.jar
do
    RABBIT_JARS="$d:$RABBIT_JARS"
done

clojurec -cp ${RABBIT_JARS} test_rabbitmq 1> /dev/null
java -cp ${RABBIT_JARS} test_rabbitmq
rm *.class

cd ${DIR}
echo '\nrabbitmq test completed succesfully\n'




