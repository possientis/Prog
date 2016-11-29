#!/bin/sh

HOME=/home/john/Prog
PATTERNS=${HOME}/polyglot/DesignPatterns
BITCOIN=${HOME}/polyglot/Bitcoin


echo 'Testing log file\n' > test.log

echo 'Testing ant ...'
${HOME}/ant/test.sh >> test.log 2>&1
if [ $? -ne 0 ]
then
  echo 'TESTING FAILED !!!'
  exit 1
fi

#echo 'Testing java ClassLoader ...'
#${HOME}/java/ijvm/greeters/test.sh >> test.log 2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#echo 'Testing Number ...'
#${BITCOIN}/Number/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#echo 'Testing bitcoinj ...'
#${HOME}/java/bitcoin/test.sh >> test.log 2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing libbitcoin ...'
#${HOME}/c++/bitcoin/test.sh >> test.log 2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#echo 'Testing scheme interpreter ...'
#${HOME}/scheme/evaluator/test.sh >> test.log 2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#echo 'Testing AbstractFactory ...'
#${PATTERNS}/AbstractFactory/test.sh >> test.log 2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Adapter ...'
#${PATTERNS}/Adapter/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Bridge ...'
#${PATTERNS}/Bridge/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Builder ...'
#${PATTERNS}/Builder/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing ChainOfResp ...'
#${PATTERNS}/ChainOfResp/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Command ...'
#${PATTERNS}/Command/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Composite ...'
#${PATTERNS}/Composite/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Decorator ...'
#${PATTERNS}/Decorator/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Facade ...'
#${PATTERNS}/Facade/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Factory ...'
#${PATTERNS}/Factory/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Filter ...'
#${PATTERNS}/Filter/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Flyweight ...'
#${PATTERNS}/Flyweight/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Interpreter ...'
#${PATTERNS}/Interpreter/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Prototype ...'
#${PATTERNS}/Prototype/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Proxy ...'
#${PATTERNS}/Proxy/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#
#echo 'Testing Singleton ...'
#${PATTERNS}/Singleton/test.sh >> test.log  2>&1
#if [ $? -ne 0 ]
#then
#  echo 'TESTING FAILED !!!'
#  exit 1
#fi
#
#


echo 'All tests completed succesfully'

