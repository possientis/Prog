#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/coq/logic
cd ${HOME}

rm -f Main
rm -f ./{*,.*}.{aux,glob,vo,o,hi}
rm -f */{*,.*}.{aux,glob,vo,o,hi}
rm -f */*/{*,.*}.{aux,glob,vo,o,hi}

cd ${DIR}
