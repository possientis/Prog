#!/bin/sh
# need libmono-system-numerics4.0-cil

set -e
DIR=${HOME}/Prog/poly/Bitcoin/Number/c#
cd ${DIR}

echo '\nThis is C# ...'
./compile.sh Test_Number.cs
START=$(date +%s%N)
mono Test_Number.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
