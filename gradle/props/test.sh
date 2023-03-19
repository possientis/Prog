#!/bin/sh

set -e 
DIR=/home/john/Prog/gradle/props
cd ${DIR}

gradle printProperties

echo '\ntest completed successfully\n'
