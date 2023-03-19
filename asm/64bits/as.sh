#!/bin/sh

name=$(basename "$1" .s)

as -g -o $name.o $name.s




