#!/bin/sh
# creates root setuid executable from c source

name=$(basename "$1" .c)

gcc -O2 -o $name $name.c hacking.c hacking-network.c
sudo chown root:root $name
sudo chmod u+s $name
