#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/haskell/logic/
cd ${HOME}

rm -f Main
rm -f ./{*,.*}.{o,hi}
rm -f */{*,.*}.{o,hi}
rm -f */*/{*,.*}.{o,hi}
rm -f */*/*/{*,.*}.{o,hi}

cd ${DIR}
