#!/bin/sh
gcc link.t.c link.c link_node.c
./a.out
rm a.out
