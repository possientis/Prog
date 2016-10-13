#!/bin/sh

DIR1=/home/john/Prog/c#
DIR2=/home/john/Prog/polyglot

grep "$1" $DIR1 -r
grep "$1" $DIR2 -r | grep '.cs'
