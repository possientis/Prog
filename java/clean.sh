#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/java
cd ${HOME}

rm -f *.class
./gcj/clean.sh
./ijvm/clean.sh
./bitcoin/clean.sh
./universe/clean.sh

cd ${DIR}
