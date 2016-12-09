#!/bin/sh

set -e
DIR=`pwd`
NAME=Number
HOME=/home/john/Prog/polyglot/Bitcoin/${NAME}
cd ${HOME}

echo '\nThis is Java ...'
cd java
./compile.sh Test_${NAME}.java
START=$(date +%s%N)
java Test_${NAME}
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
cd ..

echo '\nThis is C# ...'
cd c#
./compile.sh Test_${NAME}.cs
START=$(date +%s%N)
mono Test_${NAME}.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
cd ..


echo '\nThis is Haskell ...'
cd haskell
./compile.sh Test_${NAME}.hs
START=$(date +%s%N)
./Test_${NAME}
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
cd ..


cd ${DIR}
echo '\nAll Number tests completed successfully\n'


