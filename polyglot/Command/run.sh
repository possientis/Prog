#!/bin/sh



echo '\nThis is Java ...'
javac Command.java 
START=$(date +%s%N)
java Command 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


