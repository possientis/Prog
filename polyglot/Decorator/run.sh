#!/bin/sh

echo '\nThis is C++ ...'
g++ -std=c++14 decorator.cpp; 
START=$(date +%s%N)
./a.out; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out

echo '\nThis is Java ...'
javac Decorator.java; 
START=$(date +%s%N)
java Decorator; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is C# ...'
mcs decorator.cs; 
START=$(date +%s%N)
mono decorator.exe; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm decorator.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Decorator.scala
START=$(date +%s%N)
scala Decorator 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class



