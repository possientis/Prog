#!/bin/sh

DIR1=/home/john/Prog/

grep "$@" $DIR1 -r  | grep '\.c' \
                    | grep -v '\.cs' \
                    | grep -v '\.cpp' \
                    | grep -v '\.clj'

