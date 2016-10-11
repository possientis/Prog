#!/bin/sh

echo '\nThis is C ...'
gcc flyweight.c dict.c link.c link_node.c 
START=$(date +%s%N)
./a.out 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is C++ ...'
g++ -std=c++14 flyweight.cpp
START=$(date +%s%N)
./a.out 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out



echo '\nThis is Java ...'
javac Flyweight.java; 
START=$(date +%s%N)
java Flyweight 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is C# ...'
mcs flyweight.cs 
START=$(date +%s%N)
mono flyweight.exe 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm flyweight.exe



echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac Flyweight.scala
START=$(date +%s%N)
scala Flyweight
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is JavaScript ...'
START=$(date +%s%N)
node flyweight.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"



echo '\nThis is PHP ...'
START=$(date +%s%N)
php flyweight.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Python ...'
START=$(date +%s%N)
python3 flyweight.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby flyweight.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"



echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm flyweight.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Clojure ...'
clojurec flyweight 1> /dev/null 
START=$(date +%s%N)
java -cp .:/usr/share/java/clojure-1.6.0.jar flyweight
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is Haskell ...'
ghc -v0 flyweight.hs 
START=$(date +%s%N)
./flyweight 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm flyweight flyweight.hi flyweight.o

