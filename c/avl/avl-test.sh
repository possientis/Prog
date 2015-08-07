#!/bin/sh

#g++ avl.h -std=c++14
#g++ avl.c avlnode.c -std=c++14
g++  avlnode.h avl.h avl.t.c avl.c avlnode.c -std=c++14
./a.out
