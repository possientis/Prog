#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/set
cd ${HOME}

rm -f {Lang1,Core,Utils}/.*.aux
rm -f {Lang1,Core,Utils}/*.glob
rm -f {Lang1,Core,Utils}/*.vo

cd ${DIR}
