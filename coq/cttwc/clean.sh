#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/cttwc
cd ${HOME}

rm -f Main
rm -f ./{*,.*}.{aux,glob,vo}
rm -f */{*,.*}.{aux,glob,vo}
rm -f */*/{*,.*}.{aux,glob,vo}
rm -f */*/*/{*,.*}.{aux,glob,vo}

cd ${DIR}
