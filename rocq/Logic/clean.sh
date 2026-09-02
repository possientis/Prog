#!/bin/bash

DIR=${HOME}/Prog/rocq/Logic
cd ${DIR}

make clean > /dev/null
rm -rf *.vo *.vok *.vos *.glob .*.aux
