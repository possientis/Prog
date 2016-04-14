#!/bin/sh

echo '\nThis is C ...'
gcc flyweight.c dict.c link.c link_node.c 
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

echo '\nThis is Haskell ...'
ghc -v0 flyweight.hs 
START=$(date +%s%N)
./flyweight 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm flyweight flyweight.hi flyweight.o

