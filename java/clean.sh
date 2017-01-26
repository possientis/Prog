#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/java
cd ${HOME}

rm -f *.class
./ijvm/clean.sh
./bitcoin/clean.sh
./universe/clean.sh

cd ${DIR}
