#!/bin/sh
grep $1 ~/Prog/scm -r
grep $1 ~/Prog/polyglot/ -r | grep '\.scm'

