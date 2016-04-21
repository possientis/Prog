#!/bin/sh
grep $1 ~/Prog/php -r
grep $1 ~/Prog/polyglot/ -r | grep '\.php'

