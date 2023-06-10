#!/bin/sh

set -e 
DIR=${HOME}/Prog/ant/JavaTask
cd ${DIR}

ant
ant clean

echo '\ntest completed successfully\n'
