#!/bin/sh

rm -f *.hi *.o
ghc -v0 -O2 $@
