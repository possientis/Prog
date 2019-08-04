#!/bin/bash

PROG=/home/john/Prog
PATTERNS=${PROG}/polyglot/DesignPatterns
BITCOIN=${PROG}/polyglot/Bitcoin

echo 'Testing log file\n' > test.log

function testing () {
    echo "Testing $1 ..."
    ${PROG}/${1}/test.sh >> test.log 2>&1
    if [ $? -ne 0 ]
    then
        echo 'TESTING FAILED'
        exit 1
    fi
}

testing c
testing assembly
testing make
testing c++
testing java
testing ant
testing maven
testing gradle
testing c#
testing haskell
testing agda
testing idris
testing scheme
testing python
testing ruby
testing javascript
testing php
testing scala
testing clojure
testing sed
testing coq
testing tex
testing bison

echo 'Testing number ...'
${BITCOIN}/Number/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing abstract factory ...'
${PATTERNS}/AbstractFactory/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing adapter ...'
${PATTERNS}/Adapter/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing bridge ...'
${PATTERNS}/Bridge/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing builder ...'
${PATTERNS}/Builder/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing chain of responsibility ...'
${PATTERNS}/ChainOfResp/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing command ...'
${PATTERNS}/Command/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing composite ...'
${PATTERNS}/Composite/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing decorator ...'
${PATTERNS}/Decorator/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing facade ...'
${PATTERNS}/Facade/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing factory ...'
${PATTERNS}/Factory/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing filter ...'
${PATTERNS}/Filter/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing flyweight ...'
${PATTERNS}/Flyweight/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing interpreter ...'
${PATTERNS}/Interpreter/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing prototype ...'
${PATTERNS}/Prototype/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing proxy ...'
${PATTERNS}/Proxy/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing singleton ...'
${PATTERNS}/Singleton/test.sh >> test.log  2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'All tests completed successfully'

