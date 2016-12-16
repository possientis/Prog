#!/bin/sh
# need to install opendjk-8-jdk

# you may need to use update-alternatives --config java
# you may need to use update-alternatives --config javac

# need to install:
# libslf4j-java 
# libjcip-annotations-java
# libjsr305-java
# libprotobuf-java

# need to build secp2561 with:
# $ ./configure --enable-jni --enable-module-edch --enable-experimental

set -e 
DIR=`pwd`
HOME=/home/john/Prog/java/
cd ${HOME}

./ijvm/test.sh
./jdbc/test.sh
./slf4j/test.sh
./bitcoin/test.sh

cd ${DIR}
echo '\nAll java tests completed successfully\n'




