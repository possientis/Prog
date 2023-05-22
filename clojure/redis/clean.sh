#!/bin/sh

DIR=${HOME}/Prog/clojure/redis
cd ${DIR}

rm -f *.class
rm -f redis/*.class
rm -f redis/channel/*.class
rm -f redis/connection/*.class
rm -f redis/connection_pool/*.class
rm -f redis/protocol/*.class

