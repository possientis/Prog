#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/set
cd ${HOME}

rm -f {Lang1,Core,Utils,Normal}/.*.aux
rm -f {Lang1,Core,Utils,Normal}/*.glob
rm -f {Lang1,Core,Utils,Normal}/*.vo

cd ${DIR}
