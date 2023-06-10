#!/bin/sh

set -e 
DIR=${HOME}/Prog/ant/Lucene
cd ${DIR}

ant
ant clean

echo '\ntest completed successfully\n'
