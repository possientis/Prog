#!/bin/sh
# this file deviates from template

set -e

UNAME=Filter
LNAME=filter
HOME=/home/john/Prog/polyglot/DesignPatterns/${UNAME}

DIR=`pwd`
cd ${HOME}

echo '\nThis is C ...'
gcc ${LNAME}.c 
START=$(date +%s%N)
./a.out 2>/dev/null        
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is C++ ...'
g++ -std=c++14 ${LNAME}.cpp
START=$(date +%s%N)
./a.out 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm a.out


echo '\nThis is Java ...'
javac ${UNAME}.java 
START=$(date +%s%N)
java ${UNAME}
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is C# ...'
mcs ${LNAME}.cs 
START=$(date +%s%N)
mono ${LNAME}.exe 
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.exe;


echo '\nThis is Scala ...'
env JAVA_HOME=/usr/lib/jvm/java-7-openjdk-amd64 scalac ${UNAME}.scala
START=$(date +%s%N)
scala ${UNAME}
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is JavaScript ...'
START=$(date +%s%N)
node ${LNAME}.js
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is PHP ...'
START=$(date +%s%N)
php ${LNAME}.php
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Python ...'
START=$(date +%s%N)
python3 ${LNAME}.py
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Ruby ...'
START=$(date +%s%N)
ruby ${LNAME}.rb
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Scheme ...'
START=$(date +%s%N)
scm -b -f ${LNAME}.scm
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"


echo '\nThis is Clojure ...'
clojurec ${LNAME} 1> /dev/null
START=$(date +%s%N)
java -cp .:/usr/share/java/clojure-1.6.0.jar ${LNAME}
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm *.class


echo '\nThis is Haskell ...'
ghc -v0 ${LNAME}.hs \
  -XMultiParamTypeClasses \
  -XTypeSynonymInstances \
  -XFlexibleInstances
START=$(date +%s%N)
./${LNAME};
END=$(date +%s%N)
DIFF=$(( $END - $START ))
echo "It took $(( $DIFF / 1000000 )) ms"
rm ${LNAME} *.hi *.o

cd ${DIR}
