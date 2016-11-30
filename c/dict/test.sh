#!/bin/sh

set -e 
DIR=`pwd`
HOME=/home/john/Prog/c/dict/
cd ${HOME}

gcc dict.t.c dict.c link.c link_node.c
./a.out
rm a.out


cd ${DIR}
echo '\ntest completed succesfully\n'




