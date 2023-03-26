#!/bin/sh

DIR=/home/john/Prog/java
cd ${DIR}

rm -f *.class
./gcj/clean.sh
./ijvm/clean.sh
./bitcoin/clean.sh
./universe/clean.sh
