#!/bin/sh
# need to install texlive-latex-base texlive-humanities textlive-pictures

set -e 
DIR=/home/john/Prog/tex/
cd ${DIR}
echo

echo "testing tex documents..."

./Logic/test.sh

echo

echo '\nAll tex tests completed successfully\n'
