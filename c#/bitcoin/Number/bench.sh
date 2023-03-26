#!/bin/sh

set -e
DIR=`pwd`
HOME=/home/john/Prog/poly/Bitcoin/Number/c#
cd ${HOME}

echo '\nThis is C# ...'
./compile.sh Bench_Number.cs
START=$(date +%s%N)
mono Bench_Number.exe
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
./clean.sh
