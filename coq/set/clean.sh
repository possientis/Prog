#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/set
cd ${HOME}

rm -f {Semantics,Core,Utils}/.*.aux
rm -f {Semantics,Core,Utils}/*.glob
rm -f {Semantics,Core,Utils}/*.vo

cd ${DIR}
