#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda/vfpa  # changing 'HOME' is a bad idea
cd ${HOME1}

agda void.agda
agda maybe.agda
agda id.agda
agda bool.agda
agda sum.agda
agda relations.agda
agda nat.agda
agda min-max.agda
agda list.agda
agda vector.agda
agda bst.agda

./clean.sh

cd ${DIR}
echo '\nAll vfpa tests completed successfully\n'




