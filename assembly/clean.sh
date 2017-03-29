#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/assembly
cd ${HOME}

./32bits/clean.sh
./64bits/clean.sh

cd ${DIR}
