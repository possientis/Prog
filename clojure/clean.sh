#!/bin/sh

DIR=/home/john/Prog/clojure
cd ${DIR}

rm -f *.class
./hiccup/clean.sh
./jdbc/clean.sh
./rabbitmq/clean.sh
./redis/clean.sh

