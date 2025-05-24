#!/bin/bash

DIR=${HOME}/Prog/coq/CPDT
cd ${DIR}

rm -f Main
rm -f ./{*,.*}.{aux,glob,vo,vok,vos,o,hi}
rm -f */{*,.*}.{aux,glob,vo,vok,vos,o,hi}
rm deps


