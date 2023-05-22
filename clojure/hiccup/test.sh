#!/bin/sh

set -e 
DIR=${HOME}/Prog/clojure/hiccup
cd ${DIR}

clojurec -cp clojure.jar test_hiccup 1> /dev/null

java -cp clojure.jar:. test_hiccup

./clean.sh


echo '\nhiccup test completed successfully\n'
