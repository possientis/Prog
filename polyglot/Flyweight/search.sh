#!/bin/sh
grep $1 ~/Prog/c# -r
grep $1 ~/Prog/polyglot/ -r | grep '\.cs'

