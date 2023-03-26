#!/bin/sh
# need to install texlive-latex-base texlive-humanities textlive-pictures


set -e 
DIR=/home/john/Prog/tex/Logic/
cd ${DIR}
echo 

echo "testing the universal algebra of predicate logic..."

mv logic.pdf logic.bak

pdflatex -halt-on-error logic > /dev/null
pdflatex -halt-on-error logic > /dev/null

# two prior runs to remove warnings
pdflatex -halt-on-error logic 

./clean.sh

mv logic.bak logic.pdf

echo
cd ${DIR}
echo '\nlogic test completed successfully\n'
