#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/link
cd ${HOME}

gcc link_node.t.c link_node.c
./a.out
rm a.out


gcc link.t.c link.c link_node.c
./a.out
rm a.out


cd ${DIR}
echo '\ntest completed successfully\n'




