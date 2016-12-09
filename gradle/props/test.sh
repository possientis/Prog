#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/gradle/props
cd ${HOME}

gradle printProperties

cd ${DIR}
echo '\ntest completed successfully\n'




