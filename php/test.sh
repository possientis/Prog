#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/php/
cd ${HOME}

php hello.php

cd ${DIR}
echo '\nAll php tests completed successfully\n'




