#!/bin/sh
grep $1 ~/Prog/python -r
grep $1 ~/Prog/polyglot/ -r | grep '\.py'

