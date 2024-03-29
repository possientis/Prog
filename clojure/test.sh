#!/bin/sh

set -e 
DIR=${HOME}/Prog/clojure/
cd ${DIR}

./hiccup/test.sh
./rabbitmq/test.sh
./redis/test.sh
./jdbc/test.sh

echo '\nAll clojure tests completed successfully\n'
