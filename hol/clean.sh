#!/bin/sh

DIR=`pwd`
HOME=/home/john/Prog/hol
cd ${HOME}

rm -rf .hollogs
rm -rf .HOLMK

rm -f *Theory.*
rm -f *.uo
rm -f *.ui

./euclid/clean.sh
./parity/clean.sh

cd ${DIR}