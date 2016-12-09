#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/slf4j
cd ${HOME}

echo '\nslf4j with no binding ...'
javac -cp /usr/share/java/slf4j-api.jar SLF4JExample.java
java -cp /usr/share/java/slf4j-api.jar:. SLF4JExample

echo '\nslf4j with simple binding ...'
javac -cp /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-simple.jar \
          SLF4JExample.java

java -cp  /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-simple.jar:. \
          SLF4JExample

echo '\nslf4j with jdk14 binding ...'
javac -cp /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-jdk14.jar \
          SLF4JExample.java

java -cp  /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-jdk14.jar:. \
          SLF4JExample

echo '\nslf4j with NOP binding ...'
javac -cp /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-nop.jar \
          SLF4JExample.java

java -cp  /usr/share/java/slf4j-api.jar:/usr/share/java/slf4j-nop.jar:. \
          SLF4JExample

rm *.class

cd ${DIR}
echo '\nslf4j test completed successfully\n'




