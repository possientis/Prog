#!/bin/sh

DIR=${HOME}/Prog/hol
cd ${DIR}

rm -rf .hollogs
rm -rf .HOLMK

rm -f *Theory.*
rm -f *.uo
rm -f *.ui

./euclid/clean.sh
./parity/clean.sh

