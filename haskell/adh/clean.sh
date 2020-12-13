#!/bin/bash

DIR=/home/john/Prog/haskell/adh/
cd ${DIR}

rm -f Main
rm -f ./{*,.*}.{o,hi}
rm -f */{*,.*}.{o,hi}
rm -f */*/{*,.*}.{o,hi}
rm -f */*/*/{*,.*}.{o,hi}

