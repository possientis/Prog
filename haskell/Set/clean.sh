#!/bin/bash

DIR=/home/john/Prog/haskell/Set/
cd ${DIR}

rm -f Main
rm -f ./{*,.*}.{o,hi}
rm -f */{*,.*}.{o,hi}
rm -f */*/{*,.*}.{o,hi}
rm -f */*/*/{*,.*}.{o,hi}

