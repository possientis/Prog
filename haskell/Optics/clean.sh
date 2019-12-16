#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/haskell/Optics
cd ${HOME}

rm -f Main
rm -f ./{*,.*}.{o,hi}
rm -f */{*,.*}.{o,hi}
rm -f */*/{*,.*}.{o,hi}
rm -f */*/*/{*,.*}.{o,hi}

cd ${DIR}
