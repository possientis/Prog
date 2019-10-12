#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/set
cd ${HOME}

rm -f {Core,Utils}/.*.aux
rm -f {Core,Utils}/*.glob
rm -f {Core,Utils}/*.vo

cd ${DIR}
