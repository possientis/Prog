#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/cpdt/Haskell
cd ${HOME}

rm -f Main
rm -f ./{*,.*}.{o,hi}
rm -f */{*,.*}.{o,hi}


cd ${DIR}
