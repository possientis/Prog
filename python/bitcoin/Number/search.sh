#!/bin/sh

DIR1=/home/john/Prog/

grep "$@" $DIR1 -r | grep '\.py'
