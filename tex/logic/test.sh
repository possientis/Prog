#!/bin/sh
# need to install texlive-latex-base texlive-humanities textlive-pictures


set -e 
DIR=`pwd`
HOME=/home/john/Prog/tex/logic/
cd ${HOME}
echo 

echo "testing the universal algebra of predicate logic..."

pdflatex -halt-on-error logic > /dev/null
pdflatex -halt-on-error logic > /dev/null

# two prior runs to remove warnings
pdflatex -halt-on-error logic 

./clean.sh

echo
cd ${DIR}
echo '\nlogic test completed successfully\n'




