#!/bin/bash

DIR=/home/john/Prog/coq/cpdt/Haskell
cd ${DIR}

rm -f Main
rm -f ./{*,.*}.{o,hi}
rm -f */{*,.*}.{o,hi}
