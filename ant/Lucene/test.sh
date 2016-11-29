#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/ant/Lucene
cd ${HOME}

ant
ant clean

cd ${DIR}
echo '\ntest completed succesfully\n'




