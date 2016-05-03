#!/bin/sh
grep $1 ~/Prog/cpp -r
grep $1 ~/Prog/polyglot/ -r | grep '\.cpp'

