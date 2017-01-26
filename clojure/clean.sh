#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/clojure
cd ${HOME}

rm -f *.class
./hiccup/clean.sh
./jdbc/clean.sh
./rabbitmq/clean.sh
./redis/clean.sh

cd ${DIR}
