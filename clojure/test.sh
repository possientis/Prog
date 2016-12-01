#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/clojure/
cd ${HOME}

./hiccup/test.sh
./rabbitmq/test.sh
./redis/test.sh

cd ${DIR}
echo '\nAll clojure tests completed succesfully\n'




