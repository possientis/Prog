#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/clojure/hiccup
cd ${HOME}

clojurec -cp clojure.jar test_hiccup 1> /dev/null

java -cp clojure.jar:. test_hiccup

./clean.sh


cd ${DIR}
echo '\nhiccup test completed successfully\n'




