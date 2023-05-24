#!/bin/sh

DIR=${HOME}/Prog/java
cd ${DIR}

rm -f *.class
./gcj/clean.sh
./ijvm/clean.sh
./bitcoin/clean.sh
./universe/clean.sh
