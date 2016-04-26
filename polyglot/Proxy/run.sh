#!/bin/sh


echo '\nThis is Java ...'
javac Proxy.java 
START=$(date +%s%N)
java Proxy 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class

echo '\nThis is C# ...'
mcs proxy.cs 
START=$(date +%s%N)
mono proxy.exe 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm proxy.exe

echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Proxy.scala
START=$(date +%s%N)
scala Proxy
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is Python ...'
START=$(date +%s%N)
python3 proxy.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby proxy.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"



echo '\nThis is Haskell ...'
ghc -v0 proxy.hs 
START=$(date +%s%N)
./proxy
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm proxy proxy.o proxy.hi

