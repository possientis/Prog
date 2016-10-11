#!/bin/sh

echo '\nThis is C ...'
gcc proxy.c 
START=$(date +%s%N)
./a.out 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is C++ ...'
g++ -std=c++14 proxy.cpp
START=$(date +%s%N)
./a.out 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


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


echo '\nThis is JavaScript ...'
START=$(date +%s%N)
node proxy.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"



echo '\nThis is PHP ...'
START=$(date +%s%N)
php proxy.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"



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


echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm proxy.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Clojure ...'
clojurec proxy 1> /dev/null 
START=$(date +%s%N)
java -cp .:/usr/share/java/clojure-1.6.0.jar proxy
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is Haskell ...'
ghc -v0 proxy.hs 
START=$(date +%s%N)
./proxy
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm proxy proxy.o proxy.hi

