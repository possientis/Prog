#!/bin/sh
grep $1 ~/Prog/js -r
grep $1 ~/Prog/polyglot/ -r | grep '\.js'

