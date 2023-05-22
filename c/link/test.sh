#!/bin/sh

set -e 
DIR=${HOME}/Prog/c/link
cd ${DIR}

gcc link_node.t.c link_node.c
./a.out
rm a.out


gcc link.t.c link.c link_node.c
./a.out
rm a.out

echo '\ntest completed successfully\n'




