#!/bin/sh

echo '\nThis is Java ...'
javac Facade.java; 
START=$(date +%s%N)
java Facade; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


