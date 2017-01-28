#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/python
cd ${HOME}

rm -rf __pycache__
./bitcoin/clean.sh

cd ${DIR}
