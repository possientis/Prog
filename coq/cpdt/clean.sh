#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/cpdt
cd ${HOME}

rm -f ./{*,.*}.{aux,glob,vo} 
rm -f Test/{*,.*}.{aux,glob,vo} 
rm -f Utils/{*,.*}.{aux,glob,vo} 


cd ${DIR}
