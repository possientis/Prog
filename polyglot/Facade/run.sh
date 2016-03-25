#!/bin/sh

echo '\nThis is C ...'
gcc facade.c; 
START=$(date +%s%N)
./a.out; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is C++ ...'
g++ -std=c++14 facade.cpp; 
START=$(date +%s%N)
./a.out; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is Java ...'
javac Facade.java; 
START=$(date +%s%N)
java Facade; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is C# ...'
mcs facade.cs; 
START=$(date +%s%N)
mono facade.exe; 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm facade.exe


echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Facade.scala
START=$(date +%s%N)
scala Facade 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is JavaScript ...'
START=$(date +%s%N)
js facade.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is PHP ...'
START=$(date +%s%N)
php facade.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


