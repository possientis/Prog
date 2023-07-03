#!/bin/sh

set -e 
DIR=${HOME}/Prog/idris
cd ${DIR}
echo
echo "testing idris..."
echo

#echo "Vect..."
#idris2 --quiet --check Vect.idr 

#echo "StringOrInt..."
#idris2 --quiet --check StringOrInt.idr 

#echo "Reverse..."
#idris2 --quiet --check Reverse.idr 

#echo "replWith..."
#idris2 --quiet --check replWith.idr 

#echo "Matrix..."
#idris2 --quiet --check Matrix.idr 

#echo "ExactLength..."
#idris2 --quiet --check ExactLength.idr 

#echo "DataStore..."
#idris2 --quiet --check DataStore.idr 

make -j$(nproc --all)
./clean.sh

echo 'All idris tests completed successfully'
