#!/bin/bash

DIR=`pwd`
HOME=/home/john/Prog/haskell/mini-grin
cd ${HOME}

rm -f {Grin,Grin/Interpreter,Grin/Interpreter/Abstract,Tutorial/Chapter01}/*.{hi,o,dyn_hi,dyn_o}

cd ${DIR}
