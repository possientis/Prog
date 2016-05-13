#!/bin/sh
grep $1 . -r
grep $1 ../ -r
grep $1 ../polyglot/ -r | grep '\.scm'
