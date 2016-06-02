#!/bin/sh


echo '\nThis is Java ...'
javac Interpreter.java 
START=$(date +%s%N)
java Interpreter
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is C# ...'
mcs interpreter.cs 
START=$(date +%s%N)
mono interpreter.exe 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm interpreter.exe


