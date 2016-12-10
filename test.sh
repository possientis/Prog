#!/bin/sh

HOME=/home/john/Prog
PATTERNS=${HOME}/polyglot/DesignPatterns
BITCOIN=${HOME}/polyglot/Bitcoin

echo 'Testing log file\n' > test.log

echo 'Testing c ...'
${HOME}/c/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing assembly ...'
${HOME}/assembly/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing make ...'
${HOME}/make/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing c++ ...'
${HOME}/c++/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing java ...'
${HOME}/java/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing ant ...'
${HOME}/ant/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing maven ...'
${HOME}/maven/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing gradle ...'
${HOME}/gradle/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing c# ...'
${HOME}/c#/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing haskell ...'
${HOME}/haskell/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing scheme ...'
${HOME}/scheme/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing javascript ...'
${HOME}/javascript/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing php ...'
${HOME}/php/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi


echo 'Testing clojure ...'
${HOME}/clojure/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing coq ...'
${HOME}/coq/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

echo 'Testing logic ...'
${HOME}/logic/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

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

