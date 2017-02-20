#!/bin/sh

name=$(basename "$1" .c)

gcc -O2 -o $name $name.c hacking.c
sudo chown root:root $name
sudo chmod u+s $name
