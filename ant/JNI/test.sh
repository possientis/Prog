#!/bin/sh

set -e 
DIR=${HOME}/Prog/ant/JNI
cd ${DIR}

ant
ant clean

echo '\ntest completed successfully\n'
