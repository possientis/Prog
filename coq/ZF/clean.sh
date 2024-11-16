#!/bin/bash

DIR=${HOME}/Prog/coq/ZF
cd ${DIR}

make clean > /dev/null
rm -rf *.vo *.vok *.vos *.glob .*.aux
