#!/bin/bash

set -euo pipefail

PROG=${HOME}/Prog
POLY=${PROG}/poly
PATTERNS=${POLY}/DesignPatterns
BITCOIN=${POLY}/Bitcoin
LOGFILE="test.log"

echo -e "Testing log file\n" > "$LOGFILE"

testing () {
    local name="$1"
    echo "Testing $name ..."
    "${DIR}/${name}/test.sh" >> "$LOGFILE" 2>&1 || {
        echo "❌ TESTING FAILED in ${DIR}/${name}"
        echo "See $LOGFILE for details."
        exit 1
    }
}

DIR=${PROG}
for target in c asm make c++ java ant maven gradle \
  c# haskell coq idris scheme python ruby js php scala clojure sed tex bison
do
  testing "$target"
done

DIR=${POLY}
for target in Pascal Primes
do
  testing "$target"
done

DIR=${BITCOIN}
testing Number

DIR=${PATTERNS}
for target in AbstractFactory Adapter Bridge Builder ChainOfResp Command Composite \
    Decorator Facade Factory Filter Flyweight Interpreter Prototype Proxy Singleton
do
  testing "$target"
done

echo "✅ All tests completed successfully"

