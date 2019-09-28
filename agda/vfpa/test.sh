#!/bin/sh
# need to install agda

set -e 
DIR=`pwd`
HOME1=/home/john/Prog/agda/vfpa  # changing 'HOME' is a bad idea
cd ${HOME1}
echo
echo "testing vfpa..."

agda level.agda
agda void.agda
agda maybe.agda
agda id.agda
agda bool.agda
agda function.agda
agda sum.agda
agda prod.agda
agda relations.agda
agda nat.agda
agda square.agda
agda rewrite-test.agda
agda with-abstraction.agda
agda min-max.agda
agda list.agda
agda vector.agda
agda bst.agda
agda sigma.agda
agda z.agda
agda reflect-list.agda
agda combinator.agda

./clean.sh

cd ${DIR}
echo '\nAll vfpa tests completed successfully\n'




