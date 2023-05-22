#!/bin/sh

DIR1=${HOME}/Prog/

grep "$@" $DIR1 -r | grep '\.c' \
                   | grep -v '\.cs' \
                   | grep -v '\.clj' \
                   | grep -v '\.cpp'
