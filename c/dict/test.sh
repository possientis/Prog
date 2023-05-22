#!/bin/sh

set -e 
DIR=${HOME}/Prog/c/dict/
cd ${DIR}

gcc dict.t.c dict.c link.c link_node.c
./a.out
rm a.out

echo '\ntest completed successfully\n'




