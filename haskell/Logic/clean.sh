#!/bin/bash

DIR=${HOME}/Prog/haskell/Logic/
cd ${DIR}

rm -f Main
rm -f ./{*,.*}.{o,hi}
rm -f */{*,.*}.{o,hi}
rm -f */*/{*,.*}.{o,hi}
rm -f */*/*/{*,.*}.{o,hi}
