#!/bin/sh
# need to install texlive-latex-base texlive-humanities textlive-pictures


set -e 
DIR=`pwd`
HOME=/home/john/Prog/tex/
cd ${HOME}
echo

echo "testing tex documents..."

./logic/test.sh

echo

cd ${DIR}
echo '\nAll tex tests completed successfully\n'




