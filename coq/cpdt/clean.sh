#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/cpdt
cd ${HOME}

rm -f ./{*,.*}.{aux,glob,vo}
rm -f */{*,.*}.{aux,glob,vo}


cd ${DIR}
