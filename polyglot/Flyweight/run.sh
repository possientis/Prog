#!/bin/sh

echo '\nThis is Java ...'
javac Flyweight.java; 
START=$(date +%s%N)
java Flyweight 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


