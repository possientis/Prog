#!/bin/sh
grep $1 ~/Prog/ruby -r
grep $1 ~/Prog/polyglot/ -r | grep '\.rb'

