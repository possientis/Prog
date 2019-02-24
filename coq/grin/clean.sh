#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/coq/grin
cd ${HOME}

rm -f .*.aux
rm -f *.glob
rm -f *.vo

rm -f lib/.*.aux
rm -f lib/*.glob
rm -f lib/*.vo

cd ${DIR}
