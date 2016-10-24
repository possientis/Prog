#!/bin/sh

set -e

NAME=Number
HOME=/home/john/Prog/polyglot/Bitcoin/${NAME}

DIR=`pwd`
cd ${HOME}

echo '\nThis is Java ...'
cd java
./compile.sh Test_${NAME}.java
START=$(date +%s%N)
java Test_${NAME}
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class
cd ..

echo '\nThis is C# ...'
cd c#
./compile.sh Test_${NAME}.cs
START=$(date +%s%N)
mono Test_${NAME}.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.dll *.exe
cd ..

cd ${DIR}


