#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/clojure/hiccup
cd ${HOME}

clojurec -cp clojure-1.6.0.jar test_hiccup 1> /dev/null

java -cp clojure-1.6.0.jar:. test_hiccup

rm *.class
rm hiccup/*.class
rm hiccup/compiler/*.class
rm hiccup/util/*.class


cd ${DIR}
echo '\nhiccup test completed successfully\n'




