#!/bin/bash

DIR=${HOME}/Prog/coq/cttwc
cd ${DIR}

rm -f Main
rm -f ./{*,.*}.{aux,glob,vo,vok,vos}
rm -f */{*,.*}.{aux,glob,vo,vok,vos}
rm -f */*/{*,.*}.{aux,glob,vo,vok,vos}
rm -f */*/*/{*,.*}.{aux,glob,vo,vok,vos}

