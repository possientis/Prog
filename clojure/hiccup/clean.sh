#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/clojure/hiccup
cd ${HOME}

rm -f *.class
rm -f hiccup/*.class
rm -f hiccup/compiler/*.class
rm -f hiccup/util/*.class

cd ${DIR}
