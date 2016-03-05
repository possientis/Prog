#!/bin/sh
grep $1 ~/Prog/c -r
grep $1 ~/Prog/polyglot/ -r | grep '\.c'  # need to refine regex to exclude cpp, clj
