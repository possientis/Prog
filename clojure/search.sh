#!/bin/sh
grep $1 ~/Prog/clojure -r
grep $1 ~/Prog/polyglot/ -r | grep '\.clj'

