#!/bin/bash

DIR=${HOME}/Prog/coq/Logic
cd ${DIR}

make clean > /dev/null
rm -rf *.vo *.vok *.vos *.glob .*.aux
