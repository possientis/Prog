#!/bin/sh

echo '\nThis is Java ...'
javac ChainOfResp.java 
START=$(date +%s%N)
java ChainOfResp
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


