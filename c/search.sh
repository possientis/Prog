#!/bin/sh
grep $1 . -r
grep $1 ../polyglot/ -r | grep '\.c'  # need to refine regex to exclude cpp, clj
