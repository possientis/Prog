#!/bin/sh

set -e 
DIR=${HOME}/Prog/ant/AntTask
cd ${DIR}

ant
ant clean

echo '\ntest completed successfully\n'
