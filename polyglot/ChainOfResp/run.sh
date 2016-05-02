#!/bin/sh

echo '\nThis is Java ...'
javac ChainOfResp.java 
START=$(date +%s%N)
java ChainOfResp
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is C# ...'
mcs chainOfResp.cs 
START=$(date +%s%N)
mono chainOfResp.exe 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm chainOfResp.exe


echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac ChainOfResp.scala
START=$(date +%s%N)
scala ChainOfResp 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is PHP ...'
START=$(date +%s%N)
php chainOfResp.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Python ...'
START=$(date +%s%N)
python3 chainOfResp.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby chainOfResp.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


