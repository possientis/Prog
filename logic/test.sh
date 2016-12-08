#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/logic/
cd ${HOME}

pdflatex -halt-on-error logic > /dev/null
pdflatex -halt-on-error logic > /dev/null

# two prior runs to remove warnings
pdflatex -halt-on-error logic 

./clean.sh


cd ${DIR}
echo '\nlogic test completed succesfully\n'




