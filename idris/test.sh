#!/bin/sh

set -e 
DIR=/home/john/Prog/idris
cd ${DIR}
echo
echo "testing idris..."
echo

echo "WordLength..."
idris2 --quiet --check WordLength.idr 

echo "Vehicle..."
idris2 --quiet --check Vehicle.idr 

#echo "Vect..."
#idris2 --quiet --check Vect.idr 

echo "VecSort..."
idris2 --quiet --check VecSort.idr 

echo "TupleVect..."
idris2 --quiet --check TupleVect.idr 

echo "Tree..."
idris2 --quiet --check Tree.idr 

#echo "StringOrInt..."
#idris2 --quiet --check StringOrInt.idr 

#echo "Reverse..."
#idris2 --quiet --check Reverse.idr 

#echo "replWith..."
#idris2 --quiet --check replWith.idr 

echo "Printf..."
idris2 --quiet --check Printf.idr 

echo "Polygon..."
idris2 --quiet --check Polygon.idr 

echo "Overloading..."
idris2 --quiet --check Overloading.idr 

echo "Mutual..."
idris2 --quiet --check Mutual.idr 

echo "Matter..."
idris2 --quiet --check Matter.idr 

#echo "Matrix..."
#idris2 --quiet --check Matrix.idr 

echo "Map..."
idris2 --quiet --check Map.idr 

echo "Length..."
idris2 --quiet --check Length.idr 

echo "Hello world..."
idris2 --quiet --check Hello.idr 

echo "Expr..."
idris2 --quiet --check Expr.idr 

#echo "ExactLength..."
#idris2 --quiet --check ExactLength.idr 

echo "EqNat..."
idris2 --quiet --check EqNat.idr 

echo "DepPairs..."
idris2 --quiet --check DepPairs.idr 

#echo "DataStore..."
#idris2 --quiet --check DataStore.idr 

echo "Adder..."
idris2 --quiet --check Adder.idr 

./clean.sh

echo 'All idris tests completed successfully'




