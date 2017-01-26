#!/bin/sh

rm -f a.out
rm -f *.o
gcc -O2 $@
