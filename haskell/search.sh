#!/bin/sh
grep $1 ~/Prog/haskell -r
grep $1 ~/Prog/polyglot/ -r | grep '\.hs'
