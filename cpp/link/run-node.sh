#!/bin/sh
# there must be a way of doing this properly with a
# separate makefile. Will worry about this later
g++ -std=c++14 -o linknode linknode.t.c Ilinknode.c
./linknode
