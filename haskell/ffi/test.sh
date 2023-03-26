#!/bin/sh

gcc -c ffilib.c
ghc Main.hs -static ffilib.o
./Main

./clean.sh
