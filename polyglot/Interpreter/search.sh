#!/bin/sh
grep $1 ~/Prog/scala -r
grep $1 ~/Prog/polyglot/ -r | grep '\.scala'

