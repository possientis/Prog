#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/clojure/jdbc
cd ${HOME}

rm -f *.class 
rm -f clojure/*.class   
rm -f clojure/java/*.class 
rm -f clojure/java/jdbc/*.class

cd ${DIR}
