#!/bin/sh

set -e 
DIR=${HOME}/Prog/gradle/props
cd ${DIR}

gradle printProperties

echo '\ntest completed successfully\n'
