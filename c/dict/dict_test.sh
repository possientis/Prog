#!/bin/sh

gcc dict.t.c dict.c link.c link_node.c
./a.out
rm a.out
