#!/bin/sh

echo '\nThis is C ...'
gcc composite.c 
START=$(date +%s%N)
./a.out 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is C++ ...'
g++ -std=c++14 composite.cpp 
START=$(date +%s%N)
./a.out 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is Java ...'
javac Composite.java 
START=$(date +%s%N)
java Composite 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is C# ...'
mcs composite.cs 
START=$(date +%s%N)
mono composite.exe 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm composite.exe


echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Composite.scala
START=$(date +%s%N)
scala Composite 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is JavaScript ...'
START=$(date +%s%N)
js composite.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is PHP ...'
START=$(date +%s%N)
php composite.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"

echo '\nThis is Python ...'
START=$(date +%s%N)
python3 composite.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby composite.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm composite.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Clojure ...'
clojurec composite 1> /dev/null 
START=$(date +%s%N)
java -cp .:/usr/share/java/clojure-1.6.0.jar composite
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is Haskell ...'
ghc -v0 composite.hs 
START=$(date +%s%N)
./composite 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm composite composite.hi composite.o

