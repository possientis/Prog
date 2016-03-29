#!/bin/sh
grep $1 ~/Prog/java -r
grep $1 ~/Prog/polyglot/ -r | grep '\.java'

