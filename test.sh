#!/bin/bash


PROG=${HOME}/Prog
POLY=${PROG}/poly
PATTERNS=${POLY}/DesignPatterns
BITCOIN=${POLY}/Bitcoin

echo 'Testing log file\n' > test.log

function testing () {
    echo "Testing $1 ..."
    ${DIR}/${1}/test.sh >> test.log 2>&1
    if [ $? -ne 0 ]
    then
        echo 'TESTING FAILED'
        exit 1
    fi
}

DIR=${PROG}
testing c
testing asm
testing make
testing c++
testing java
testing ant
testing maven
testing gradle
testing c#
testing haskell
testing coq
testing agda
#testing lean
testing idris
testing scheme
testing python
testing ruby
testing js
testing php
testing scala
testing clojure
testing sed
testing tex
testing bison

DIR=${POLY}
testing Pascal
testing Primes

DIR=${BITCOIN}
testing Number

DIR=${PATTERNS}
testing AbstractFactory
testing Adapter
testing Bridge
testing Builder
testing ChainOfResp
testing Command
testing Composite
testing Decorator
testing Facade
testing Factory
testing Filter
testing Flyweight
testing Interpreter
testing Prototype
testing Proxy
testing Singleton

echo 'All tests completed successfully'

