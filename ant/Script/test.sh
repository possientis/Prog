#!/bin/sh

# probably need to install the JVM based javascript interpreter rhino

set -e 
DIR=${HOME}/Prog/ant/Script
cd ${DIR}

ant

echo '\ntest completed successfully\n'
