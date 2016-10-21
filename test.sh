#!/bin/sh

HOME=/home/john/Prog
PATTERNS=${HOME}/polyglot/DesignPatterns

set -e  # exit script on error

echo '\n\nTesting bitcoinj ...'
${HOME}/java/bitcoin/test.sh

echo '\n\nTesting AbstractFactory ...'
${PATTERNS}/AbstractFactory/run.sh

echo '\n\nTesting Adapter ...'
${PATTERNS}/Adapter/run.sh

echo '\n\nAll tests completed succesfully'

