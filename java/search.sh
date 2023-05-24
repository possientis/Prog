#!/bin/sh

DIR1=${HOME}/Prog/

grep "$@" $DIR1 -r | grep '\.java'
