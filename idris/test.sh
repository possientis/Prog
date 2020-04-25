#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/idris
cd ${HOME}
echo
echo "testing idris..."
echo

echo "WordLength..."
idris WordLength.idr --check

echo "Vehicle..."
idris Vehicle.idr --check

echo "Vect..."
idris Vect.idr --check

echo "VecSort..."
idris VecSort.idr --check

echo "TupleVect..."
idris TupleVect.idr --check

echo "Tree..."
idris Tree.idr --check

echo "StringOrInt..."
idris StringOrInt.idr --check

echo "Reverse..."
idris Reverse.idr --check

echo "replWith..."
idris replWith.idr --check

echo "Printf..."
idris Printf.idr --check

echo "Polygon..."
idris Polygon.idr --check

echo "Overloading..."
idris Overloading.idr --check

echo "Mutual..."
idris Mutual.idr --check

echo "Matter..."
idris Matter.idr --check

echo "Matrix..."
idris Matrix.idr --check

echo "Map..."
idris Map.idr --check

echo "Length..."
idris Length.idr --check

echo "Hello world..."
idris Hello.idr --check

echo "Expr..."
idris Expr.idr --check

echo "ExactLength..."
idris ExactLength.idr --check

echo "EqNat..."
idris EqNat.idr --check

echo "DepPairs..."
idris DepPairs.idr --check

echo "DataStore..."
idris DataStore.idr --check

echo "Adder..."
idris Adder.idr --check

./clean.sh

cd ${DIR}
echo '\nAll idris tests completed successfully\n'




